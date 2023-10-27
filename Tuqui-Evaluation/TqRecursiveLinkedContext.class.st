Class {
	#name : #TqRecursiveLinkedContext,
	#superclass : #TqLinkedContext,
	#instVars : [
		'nonLocalReturn'
	],
	#category : #'Tuqui-Evaluation-Runtime'
}

{ #category : #'as yet unclassified' }
TqRecursiveLinkedContext >> evaluateFor: interpreter [
	| sexpressions result |
	nonLocalReturn := [ :value | 
	interpreter context: self homeContext parent.
	^ value ].
	sexpressions := runtime sexpressionsOf: method.
	result := interpreter visitMethod: sexpressions.
	interpreter context: self parent.
	^ result
]

{ #category : #initialization }
TqRecursiveLinkedContext >> initializeForBlock: tqBlock args: blockArguments closure: tqClosure [ 
	arguments := blockArguments.
	method := tqBlock.
	environment := tqClosure.
]

{ #category : #'as yet unclassified' }
TqRecursiveLinkedContext >> return: anObject [
	^self isBlock
		ifTrue: [ nonLocalReturn value: anObject ]
		ifFalse: [ anObject ]
]
