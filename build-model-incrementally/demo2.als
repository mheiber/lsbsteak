// using custom build of alloy that enables custom visualizations
sig MethodName {}
// We treat __construct as a special static method.
// Constructors are like static methods from the *caller's* point of view
// since they are callable things defined on the class that don't require an instance
one sig __Construct in MethodName {}

abstract sig Method {
  method_name: one MethodName,
}

// On the representation of methods of a class:
// - "inheritance" is when two classes share a method
// - "overriding" is when subclass has a class with the same name as the name of a class in the parent
abstract sig Class {
   methods: set Method,
   parent: lone Class
}

sig AbstractClass, ConcreteClass extends Class {}

sig ConcreteMethod extends Method {
    calls: set Call
}


sig AbstractMethod extends Method {}

sig Call {
   receiver: Receiver,
   call_method_name: MethodName,
}




abstract sig Receiver {}

/**
We are not modeling C::foo() directly, but you can see from 
the proposal that C::foo() is treated the same way as `(C::class)::foo()`.

We are not modeling `$cls = static::class;` and instead are only modeling
direct `static::foo()` calls. I suspect nothing hinges on this choice
*/
sig Var extends Receiver {
   var_points_to: one (Var + Class)
}

one sig StaticKeyword extends Receiver {}


// well-formedness

fact "no class is its own ancestor" {
   no c: Class | c in c.^parent
}

fact "all methods are in classes, all `MethodName`s name a method" {
  all m: Method | some c: Class | m in c.methods
  all mn: MethodName | some m: Method | m.method_name = mn
}

fact "all concrete classes have concrete constructors, no abstract classes have concrete constructors" {
  all c: Class | __Construct in (c.methods & ConcreteMethod).method_name iff c in ConcreteClass
}

fact "each static:: call is in a single method. And (ease of reading) other calls are outside methods" {
  all call: Call | call.receiver = StaticKeyword iff one m: Method | call in m.calls
}

fact "concrete classes cannot contain abstract methods" {
  no ConcreteClass.methods & AbstractMethod
}

fact "concrete classes must have implementations for all methods" {
    ConcreteClass.methods in ConcreteMethod
}

fact "a class must have all the method names of its parent" {
   all class: Class |
    (class.parent.methods.method_name - __Construct)
    in class.methods.method_name
}

fact "methods are only inherited from parents" {
  all disj class1, class2: Class |
  all m: class1.methods |
  m in class2.methods implies
      (class1 in class2.parent or class2 in class1.parent)
}

fact "A variable that names a class must have come (transitively) from naming a class" {
  all v: Var | one class: Class | class in v.^var_points_to
}

fact "method names are unique in a class" {
  all c: Class | all disj m1, m2: c.methods |
  disj[m1.method_name, m2.method_name]
}

run {}

run {
  some c1, c2: Class | c1.parent = c2
}