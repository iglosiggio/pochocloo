Class {
	#name : #TqEvaluationTest,
	#superclass : #TestCase,
	#instVars : [
		'runtime',
		'bootstrapper'
	],
	#category : #'Tuqui-Tests'
}

{ #category : #tests }
TqEvaluationTest >> ==> anObject [
	| class |
	class := anObject class.
	anObject isInteger
		ifTrue: [ ^ runtime newInteger: anObject ].
	anObject == nil
		ifTrue: [ ^ runtime nil ].
	anObject == false
		ifTrue: [ ^ runtime false ].
	anObject == true
		ifTrue: [ ^ runtime true ].
	(class == Symbol or: [ class inheritsFrom: Symbol ])
		ifTrue: [ ^ runtime symbolFromLocal: anObject ].
	anObject isString
		ifTrue: [ ^ runtime newString: anObject ].
	class = ByteArray
		ifTrue: [ ^ runtime newBytesFrom: anObject ].
	self ASSERT: false
]

{ #category : #tests }
TqEvaluationTest >> assertNoLeftoverFrames [
	self assert: runtime currentEvaluator hasFinished
]

{ #category : #tests }
TqEvaluationTest >> compile: aString in: classname during: aBlock [

	| class behavior md selector method |
	class := self globalNamed: classname.
	behavior := runtime speciesInstanceBehavior: class.
	md := runtime behaviorMethodDictionary: behavior.
	method := SCompiler new compile: aString.
	self assert: method notNil.
	method := bootstrapper transferMethod: method in: class.
	selector := method slotAt: 5.
	runtime sendLocal: #at:put: to: md with: {
			selector.
			method }.
	aBlock value
]

{ #category : #tests }
TqEvaluationTest >> convert: anObject with: map [
	map at: anObject ifPresent: [:mapped | ^mapped ].
	anObject ifNil: [ ^runtime nil ].
	anObject isInteger
		ifTrue: [ ^ runtime newInteger: anObject ].
	anObject isSymbol
		ifTrue: [ ^ runtime addSymbol: anObject ].
	anObject isString
		ifTrue: [ ^ runtime newString: anObject ].
	anObject class = ByteArray
		ifTrue: [ ^ runtime newByteArray: anObject ].
	anObject class = SCompiledBlock ifTrue: [ ^self convertBlock: anObject with: map ].
	self ASSERT: false
]

{ #category : #tests }
TqEvaluationTest >> convertBlock: anSCompiledBlock with: map [
	| class result instsize slot |
	class := self globalNamed: #CompiledBlock.
	result := runtime newSlots: class size: 0.
	map at: anSCompiledBlock put: result.
	instsize := anSCompiledBlock class instSize.
	1 to: instsize do: [ :i | 
		slot := anSCompiledBlock instVarAt: i.
		result slotAt: i put: (self convert: slot with: map) ].
	^ result
]

{ #category : #tests }
TqEvaluationTest >> convertMethod: anSCompiledMethod [
	| class |
	
	class := bootstrapper classNamed: anSCompiledMethod classBinding name.
	^bootstrapper transferMethod: anSCompiledMethod in: class 
]

{ #category : #tests }
TqEvaluationTest >> globalNamed: aSymbol [
	^bootstrapper classNamed: aSymbol
]

{ #category : #running }
TqEvaluationTest >> setUp [

	bootstrapper := TuquiRingBootstrapper new.
	runtime := bootstrapper genesis image.
	runtime useRecursiveEvaluator.
]

{ #category : #tests }
TqEvaluationTest >> test100yourself [
	| result |
	result := runtime sendLocal: #yourself to: runtime nil.
	self assert: result equals: runtime nil
]

{ #category : #tests }
TqEvaluationTest >> test110compute1plus1 [
	| one result |
	one := self ==> 1.
	result := runtime sendLocal: #+ to: one with: {one}.
	self assert: result equals: self ==> 2; assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test111compute1minus1 [
	| one result |
	one := self ==> 1.
	result := runtime sendLocal: #- to: one with: {one}.
	self assert: result equals: self ==> 0
]

{ #category : #tests }
TqEvaluationTest >> test112compute3times4 [
	| result |
	result := runtime sendLocal: #* to: self ==> 3 with: {self ==> 4}.
	self assert: result equals: self ==> 12
]

{ #category : #tests }
TqEvaluationTest >> test113compute20quotient5 [
	|  result |

	result := runtime sendLocal: #// to: self ==>20 with: {self ==>5}.
	self assert: result equals: self ==>4
]

{ #category : #tests }
TqEvaluationTest >> test130sendIfTrueToFalse [
	| result |
	self
		compile: 'foo ^false ifTrue: [#failed]'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: runtime nil ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test131sendIfFalseToTrue [
	| result |
	self
		compile: 'foo ^true ifFalse: [#failed]'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: runtime nil ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test132sendIfTrueToTrue [
	| result |
	self
		compile: 'foo ^true ifTrue: [5]'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 5 ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test140evaluateClosure [
	| result |
	self
		compile: 'foo ^[5] value'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 5 ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test141evaluateClosureFrames [
	| result |
	self
		compile: 'foo [5] value'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: runtime true ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test150sendWhileTrue [
	| result |
	self
		compile:
			'foo
			 | a |
			a := true.
			[a] whileTrue: [a := false].
			^a'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: runtime false ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test151sendToDo [
	| result |
	self
		compile:
			'foo
			 | a |
			a := 0.
			3 to: 4 do: [:i | a := a + i].
			^a'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 7 ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test152compute20dividedBy5 [
	| result |
	result := runtime sendLocal: #/ to: self ==> 20 with: {(self ==> 5)}.
	self 
		assert: result equals: self ==> 4;
		assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test161evaluateClosureWithArgs [
	| result |
	self
		compile: 'foo ^[:a :b | a + b] value: 3 value: 4'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 7 ]
]

{ #category : #tests }
TqEvaluationTest >> test162evaluateClosureWithArgsAndTemps [
	| result |
	self
		compile: 'foo ^[:a :b | | t | t := a + b. t] value: 3 value: 4'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 7 ]
]

{ #category : #tests }
TqEvaluationTest >> test163evaluateClosureWithArgsAndMethodTemps [
	| result |
	self
		compile: 'foo | t | ^[:a :b | t := a + b. t] value: 3 value: 4'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 7 ]
]

{ #category : #tests }
TqEvaluationTest >> test164evaluateClosureWithArgsAndMultipleTemps [
	| result |
	self
		compile:
			'foo 
				| s |
				s := 3.
				^[:a | | t | 
					t := a.
					t := t + s.
					t] value: 4'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 7 ]
]

{ #category : #tests }
TqEvaluationTest >> test165evaluateClosureNonLocalReturn [
	| result |
	self
		compile:
			'foo 
				| s |
				[s := 3. ^s] value.
				s := 4.
				^s'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 3 ]
]

{ #category : #tests }
TqEvaluationTest >> test166evaluateNestedClosure [
	| result |
	self
		compile: 'foo ^[ [ 7 ] value ] value'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 7 ]
]

{ #category : #tests }
TqEvaluationTest >> test167evaluateNestedClosureWithArgs [
	| result |
	self
		compile: 'foo ^[:a | [:b | a + b ] value: 4 ] value: 3'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 7 ]
]

{ #category : #tests }
TqEvaluationTest >> test168evaluateNestedClosureWithTemps [
	| result |
	self
		compile:
			'foo 
			| a |
			a := 2.
			^[ | b |
				b := 3.
				[ | c |
				c := 4.
				a + b + c ] value] value'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 9 ]
]

{ #category : #tests }
TqEvaluationTest >> test169evaluateInlinedClosureInClosureWithMethodTemps [
	| result |
	self
		compile:
			'foo 
			| a result |
			a := 3.
			[ true ifTrue: [ result := a + 4 ] ] value.
			^result'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result equals: self ==> 7 ]
]

{ #category : #tests }
TqEvaluationTest >> test180evaluateToDo [
	| result |
	self
		compile:
			'foo | result | result := 0. 1 to: 5 do: [:i | result := result + i]. ^result'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self
				assert: result isImmediate;
				assert: result value equals: 1 + 2 + 3 + 4 + 5 ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test190evaluateStringConcatenation [
	| result |
	self
		compile: 'foo ^''ABC'', ''DE'''
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self assert: result asLocalString equals: 'ABCDE' ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test200createDictionary [
	| class d |
	class := self globalNamed: #Dictionary.
	d := runtime sendLocal: #new to: class with: {}.
	self
		assert: d localClassName equals: 'Dictionary';
		assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test210addAssociationToDictionary [
	| class symbol assoc d |
	class := self globalNamed: #Dictionary.
	symbol := runtime addSymbol: #foo.
	assoc := runtime sendLocal: #-> to: symbol with: { runtime nil }.
	d := runtime sendLocal: #new to: class with: {}.
	runtime sendLocal: #add: to: d with: {assoc}.
	self
		assert: d localClassName equals: 'Dictionary';
		assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test300smallIntegerPrintString [
	| result |
	self
		compile: 'foo | result | result := 16r1000 printString. ^result'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self
				assert: result isBytes;
				assert: result value asLocalString equals: 16r1000 printString ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test301smallIntegerPrintString [
	| result |
	self
		compile: 'foo | result | result := 4611686018427387903 printString. ^result'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self
				assert: result isBytes;
				assert: result value asLocalString equals: 4611686018427387903 printString ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test302smallIntegerPrintString [
	| result |
	self
		compile: 'foo | result | result := -4. ^result printString'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self
				assert: result isBytes;
				assert: result value asLocalString
					equals: -4 printString ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test310smiFallbackToLNI [
	| result |
	self
		compile:
			'foo | result | result := (16r100000000 * -16r100000000) printString. ^result'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			self
				assert: result isBytes;
				assert: result value asLocalString
					equals: (16r100000000 * -16r100000000) printString ].
	self assertNoLeftoverFrames
]

{ #category : #tests }
TqEvaluationTest >> test310smiFallbackToLPI [
	| result expected |
	self
		compile:
			'foo | result | result := 1. 18 timesRepeat: [result := result * 10]. ^result printString'
		in: #ProtoObject
		during: [ result := runtime sendLocal: #foo to: runtime true.
			expected := 1.
			18 timesRepeat: [ expected := expected * 10 ].
			self
				assert: result isBytes;
				assert: result value asLocalString equals: expected printString ].
	self assertNoLeftoverFrames
]