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

sig ConcreteMethod extends Method {}


sig AbstractMethod extends Method {}

run {}