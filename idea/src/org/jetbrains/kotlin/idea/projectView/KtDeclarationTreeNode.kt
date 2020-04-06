/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */
package org.jetbrains.kotlin.idea.projectView

import com.intellij.application.options.CodeStyle
import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.projectView.ViewSettings
import com.intellij.ide.projectView.impl.nodes.AbstractPsiBasedNode
import com.intellij.ide.util.treeView.AbstractTreeNode
import com.intellij.openapi.project.Project
import com.intellij.psi.PsiElement
import com.intellij.psi.search.PsiElementProcessor
import com.intellij.psi.util.PsiTreeUtil
import org.jetbrains.kotlin.idea.KotlinBundle.message
import org.jetbrains.kotlin.idea.core.formatter.KotlinCodeStyleSettings
import org.jetbrains.kotlin.psi.*
import java.util.*

internal class KtDeclarationTreeNode(
    project: Project?,
    ktDeclaration: KtDeclaration?,
    viewSettings: ViewSettings?
) : AbstractPsiBasedNode<KtDeclaration?>(project, ktDeclaration!!, viewSettings) {

    override fun extractPsiFromValue(): PsiElement? = value

    override fun getChildrenImpl(): Collection<AbstractTreeNode<*>> {
        val settings = settings
        val project = project

        if (!settings.isShowMembers) return emptyList()
        val blockExpression = (value as? KtFunction)?.bodyBlockExpression ?: return emptyList()

        fun isFunctionOrProperty(element: PsiElement): Boolean {
            if (element is KtNamedFunction && element !is KtFunctionLiteral) return true

            if (element !is KtProperty) return false
            val parentOfParentOfBlock = (element.parent as? KtBlockExpression)?.parent ?: return false
            return parentOfParentOfBlock is KtClassOrObject || parentOfParentOfBlock is KtFile
        }

        val result: MutableList<AbstractTreeNode<*>> = ArrayList()
        PsiTreeUtil.processElements(blockExpression, PsiElementProcessor { element: PsiElement ->
            if (element !is KtDeclaration) return@PsiElementProcessor true

            val node = when {
                element is KtClassOrObject -> {
                    KtClassOrObjectTreeNode(
                        project = project,
                        ktClassOrObject = element,
                        viewSettings = settings
                    )
                }
                isFunctionOrProperty(element) -> {
                    KtDeclarationTreeNode(
                        project = project,
                        ktDeclaration = element,
                        viewSettings = settings
                    )
                }
                else -> null
            }

            if (node != null) result.add(node)
            true
        })
        return result
    }

    override fun updateImpl(data: PresentationData) {
        val declaration = value ?: return
        val project = project ?: return

        val name = (if (declaration is KtAnonymousInitializer) CLASS_INITIALIZER else declaration.name) ?: return
        if (declaration !is KtProperty && declaration !is KtFunction) {
            data.presentableText = name
            return
        }

        val settings = CodeStyle.getSettings(project).getCustomSettings(KotlinCodeStyleSettings::class.java)
        fun StringBuilder.appendColon() {
            if (settings.SPACE_BEFORE_TYPE_COLON) append(" ")
            append(":")
            if (settings.SPACE_AFTER_TYPE_COLON) append(" ")
        }

        if (declaration is KtProperty) {
            data.presentableText = buildString {
                append(name)
                declaration.typeReference?.text?.let { reference ->
                    appendColon()
                    append(reference)
                }
            }
            return
        }

        if (declaration is KtFunction) {
            data.presentableText = buildString {
                declaration.receiverTypeReference?.text?.let { receiverReference ->
                    append(receiverReference)
                    append('.')
                }
                append(name)
                append("(")
                val valueParameters = declaration.valueParameters
                valueParameters.forEachIndexed { index, parameter ->
                    parameter.name?.let { parameterName ->
                        append(parameterName)
                        appendColon()
                    }
                    parameter.typeReference?.text?.let { typeReference ->
                        append(typeReference)
                    }
                    if (index != valueParameters.size - 1) {
                        append(", ")
                    }
                }
                append(")")

                declaration.typeReference?.text?.let { returnTypeReference ->
                    appendColon()
                    append(returnTypeReference)
                }
            }
        }
    }

    override fun expandOnDoubleClick(): Boolean = false

    override fun isDeprecated(): Boolean = value?.let { KtPsiUtil.isDeprecated(it) } ?: false

    companion object {
        private val CLASS_INITIALIZER = "<" + message("project.view.class.initializer") + ">"
    }
}