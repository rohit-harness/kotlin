// TARGET_BACKEND: JVM
// WITH_RUNTIME

fun Throwable.test(): Boolean {
    var klass: Class<out Any?> = this.javaClass
    klass = klass.superclass ?: return false
    return true
}

fun box() = "OK"