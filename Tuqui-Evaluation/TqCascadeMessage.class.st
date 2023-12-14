Class {
	#name : #TqCascadeMessage,
	#superclass : #TqExpression,
	#instVars : [
		'selector',
		'arguments',
		'cascade',
		'cache'
	],
	#category : #'Tuqui-Evaluation-SExpressions'
}

{ #category : #unclassified }
TqCascadeMessage class >> decodeUsing: anAstcodeDecoder [
	^anAstcodeDecoder decodeCascadeMessage
]

{ #category : #accessing }
TqCascadeMessage >> acceptVisitor: visitor [
	^ visitor visitCascadeMessage: self
]

{ #category : #accessing }
TqCascadeMessage >> argumentCount [
	^arguments size
]

{ #category : #accessing }
TqCascadeMessage >> arguments [
	^arguments
]

{ #category : #accessing }
TqCascadeMessage >> arguments: aCollection [
	arguments := aCollection
]

{ #category : #accessing }
TqCascadeMessage >> cache: anSCompiledMethod when: type [
	cache ifNil: [ ^ cache := Array with: type with: anSCompiledMethod ].
	cache := cache , (Array with: type with: anSCompiledMethod)
]

{ #category : #accessing }
TqCascadeMessage >> cacheUndermessage: aBlockClosure [
	cache := aBlockClosure
]

{ #category : #accessing }
TqCascadeMessage >> cachedUndermessage [
	^ cache isBlock
		ifTrue: [ cache ]
]

{ #category : #accessing }
TqCascadeMessage >> cascade [ ^
	cascade
]

{ #category : #accessing }
TqCascadeMessage >> cascade: anSCascade [
	cascade := anSCascade
]

{ #category : #accessing }
TqCascadeMessage >> flushCache [
	cache := nil
]

{ #category : #accessing }
TqCascadeMessage >> isCascadeMessage [
	^true
]

{ #category : #cache }
TqCascadeMessage >> lookupFor: behavior ifAbsent: lookup [
	| method |
	cache ifNotNil: [
		| replaceIdx |
		behavior = (cache at: 1) ifTrue: [ ^ cache at: 2 ].
		behavior = (cache at: 3) ifTrue: [ ^ cache at: 4 ].
		replaceIdx := (cache at: 3)
			ifNil: [  2 ]
			ifNotNil: [ SharedRandom globalGenerator nextInteger: 2 ].
		cache at: replaceIdx * 2 - 1 put: behavior.
		cache at: replaceIdx * 2 put: lookup value.
	].
	cache := { behavior. method := lookup value. nil. nil }.
	^ method.
]

{ #category : #accessing }
TqCascadeMessage >> methodFor: requiredType [
	| type |
	cache ifNil: [ ^ nil ].
	1 to: cache size by: 2 do: [ :i | 
		type := cache at: i.
		type == requiredType
			ifTrue: [ ^ cache at: i + 1 ] ].
	^ nil
]

{ #category : #accessing }
TqCascadeMessage >> receiver [
	^cascade receiver
]

{ #category : #accessing }
TqCascadeMessage >> registerCacheWith: runtime [
	cache ifNil: [ runtime registerCache: self for: selector ]
]

{ #category : #accessing }
TqCascadeMessage >> selector [
	^selector
]

{ #category : #accessing }
TqCascadeMessage >> selector: aSymbol [
	selector := aSymbol
]
