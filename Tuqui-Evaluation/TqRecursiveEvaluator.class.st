Class {
	#name : #TqRecursiveEvaluator,
	#superclass : #TqEvaluator,
	#category : #'Tuqui-Evaluation-Runtime'
}

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateClosure: receiver whileFalse: arg [
	| result |
	[ result := self evaluateClosure: receiver.
	self booleanFrom: result ]
		whileFalse: [ self evaluateClosure: arg ].
	^ receiver
]

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateClosure: receiver whileTrue: arg [
	| result |
	[ result := self evaluateClosure: receiver.
	self booleanFrom: result ] whileTrue: [ self evaluateClosure: arg ].
	^ receiver
]

{ #category : #private }
TqRecursiveEvaluator >> evaluateClosure: closure withArgs: arguments [

	| block sblock receiver result |
	block := runtime closureBlock: closure.
	sblock := runtime blockExecutableCode: block.
	receiver := (runtime blockCapturesSelf: block)
		            ifTrue: [ closure at: 1 ]
		            ifFalse: [ nilObj ].
	context := TqRecursiveLinkedContext new
		           runtime: runtime;
		           beBlock;
		           parent: context;
		           self: receiver;
		           initializeForBlock: block
		           args: arguments
		           closure: closure.
	result := nilObj.
	sblock statements do: [ :node | result := node acceptVisitor: self ].
	^ result
]

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateSend: symbol to: receiver with: anArray [

	^self
		       send: symbol
		       to: receiver
		       with: anArray
		       super: false
]

{ #category : #visiting }
TqRecursiveEvaluator >> hasFinished [
	^context isNil
]

{ #category : #utilities }
TqRecursiveEvaluator >> lookup: symbol on: behavior [ 
	| methodDict superclassBehavior |
	methodDict := runtime behaviorMethodDictionary:  behavior.
	superclassBehavior  :=  runtime behaviorNext: behavior.
	^ methodDict atKey: symbol ifAbsent: [^ self lookup: symbol on: superclassBehavior].
]

{ #category : #visiting }
TqRecursiveEvaluator >> lookup: message on: behavior sendSite: messageAST [ 
	^ messageAST lookupFor: behavior ifAbsent: [
		runtime lookupSymbol: message forBehavior: behavior ifAbsentPut: [
			self lookup: message on: behavior]].
]

{ #category : #controlling }
TqRecursiveEvaluator >> send: symbol to: receiver with: arguments super: isSuper [
	| behavior method ast environmentSize environment |
	behavior := isSuper
		ifTrue: [ runtime superBehaviorOf: context classBinding ]
		ifFalse: [ runtime behaviorOf: receiver ].
	method := self lookup: symbol on: behavior.
	ast := runtime sexpressionsOf: method.

	"method isBlock ifTrue: [ ^ method value: receiver value: arguments ]."

	environmentSize  := runtime methodEnvironmentSize: method.
	environment := runtime newEnvironmentSized: environmentSize.
	context := TqRecursiveLinkedContext new
		runtime: runtime;
		self: receiver;
		arguments: arguments;
		environment: environment;
		parent: context;
		method: method.

	^ context evaluateFor: self.
]

{ #category : #visiting }
TqRecursiveEvaluator >> send: symbol to: receiver with: arguments super: isSuper sendSite: messageAST [
	| behavior method ast environmentSize environment |
	behavior := isSuper
		ifTrue: [ runtime superBehaviorOf: context classBinding ]
		ifFalse: [ runtime behaviorOf: receiver ].
	method := self lookup: symbol on: behavior sendSite: messageAST.
	ast := runtime sexpressionsOf: method.

	"method isBlock ifTrue: [ ^ method value: receiver value: arguments ]."

	environmentSize  := runtime methodEnvironmentSize: method.
	environment := runtime newEnvironmentSized: environmentSize.
	context := TqRecursiveLinkedContext new
		runtime: runtime;
		self: receiver;
		arguments: arguments;
		environment: environment;
		parent: context;
		method: method.

	^ context evaluateFor: self.
]

{ #category : #visiting }
TqRecursiveEvaluator >> superBehaviorOf: class [

	| superclass |
	superclass := self speciesSuperclass: class.
	^ self speciesInstanceBehavior: superclass
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitAssignment: assignmentAST [
	| value |
	value := assignmentAST expression acceptVisitor: self.
	assignmentAST assignees do: [ :assignee | assignee binding  assign: value within: self context ].
	 ^ value
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitBlock: blockAST [ 
	^ self context captureClosure: blockAST.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitCascade: cascadeAST [
	| receiver lastResult | 
	lastResult := nil.
	receiver :=  cascadeAST receiver acceptVisitor: self.
	cascadeAST messages do: [ :message | lastResult := self visiteCascadeMessage: message for: receiver. ].
	self assert: lastResult isNotNil.
	^ lastResult.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitIdentifier: identifierAST [
	^ identifierAST binding valueWithin: self context.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitLiteral: literalAST [ 
	^ literalAST value.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitMessage: messageAST [
	| isSuper receiver arguments selector |
	isSuper := messageAST receiver isSuper.
	receiver := messageAST receiver acceptVisitor: self.
	arguments := messageAST arguments collect: [ :argumentAST | argumentAST acceptVisitor: self ].
	selector := messageAST selector.
	undermessages at: selector ifPresent: [ :v | ^ v value: receiver value: arguments ].
	"TODO: Soportar super"
	^ self send: selector to: receiver  with: arguments super: isSuper sendSite: messageAST
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitMethod: methodAST [
	| primitive |
	primitive := methodAST primitive.
	primitive ifNotNil: [ ^ (primitives at: primitive) value ].
	^ self visitStatements: methodAST statements.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitReturn: returnAST [
	| result |
	result := returnAST expression acceptVisitor: self.
	returnAST local ifFalse: [ ^ self context return: result ].
	context := context parent.
	^ result
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitStatements: statements [ 
	| lastStatementAST lastResult |
	lastStatementAST := nil. lastResult := nil.

	statements do: [ :statementAST |
		lastStatementAST := statementAST.
		lastResult := statementAST acceptVisitor: self ].
	(lastStatementAST isNotNil and: [ lastStatementAST isReturn ])
		ifTrue: [ ^ lastResult ]
		ifFalse: [ ^ context receiver ].
]

{ #category : #visiting }
TqRecursiveEvaluator >> visiteCascadeMessage: cascadeMessageAST for: receiver [ 
	| arguments selector |
	selector := cascadeMessageAST selector.
	arguments := cascadeMessageAST arguments collect: [ :arg | arg acceptVisitor: self ].
	"TODO: SUPER!!!"
	^ self send: selector to: receiver with: arguments super: false sendSite: cascadeMessageAST.
]
