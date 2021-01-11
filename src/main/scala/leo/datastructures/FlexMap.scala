package leo.datastructures

trait FlexMap {
  import collection.mutable

  type Key[+A,-B]

  def createKey[A,B](): Key[A,B]
  def createKeyWithDefault[A,B](default: B): Key[A,B]
  def apply[A,B](key: Key[A,B]): mutable.Map[A, B]

  def setDefault[A,B](key: Key[A,B], default: B): Unit
}
object FlexMap {
  def apply(): FlexMap = new FlexMap {
    import collection.mutable
    override type Key[+A,-B] = Int

    private[this] var currentKey: Key[Any, Any] = 0
    private[this] final val map0: mutable.Map[Key[Any,Any], mutable.Map[Any,Any]] = mutable.Map.empty

    override final def createKey[A, B](): Key[A,B] = {
      val result = currentKey
      map0 += (result -> mutable.Map[Any,Any]())
      currentKey += 1
      result
    }

    override final def createKeyWithDefault[A, B](default: B): Key[A,B] = {
      val result = currentKey
      map0 += (result -> mutable.Map[Any,Any]().withDefaultValue(default))
      currentKey += 1
      result
    }

    override final def setDefault[A,B](key: Key[A,B], default: B): Unit = {
      val map: mutable.Map[Any,Any] = apply(key)
      map0 += (key -> map.withDefaultValue(default))
    }

    override final def apply[A, B](key: Key[A,B]): mutable.Map[A, B] = {
      map0(key).asInstanceOf[mutable.Map[A,B]]
    }
  }
}
