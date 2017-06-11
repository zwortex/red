Red/System [
	Title:   "Struct! datatype runtime functions"
	Author:  "Nenad Rakocevic"
	File: 	 %struct.reds
	Tabs:	 4
	Rights:  "Copyright (C) 2017 Nenad Rakocevic. All rights reserved."
	License: {
		Distributed under the Boost Software License, Version 1.0.
		See https://github.com/red/red/blob/master/BSL-License.txt
	}
]

_struct: context [
	verbose: 0
	
	#enum struct-types [
		STRUCT_TYPE_CHAR8
		STRUCT_TYPE_CHAR16
		STRUCT_TYPE_CHAR32
		STRUCT_TYPE_INT8
		STRUCT_TYPE_INT16
		STRUCT_TYPE_INT32
		STRUCT_TYPE_FLOAT32
		STRUCT_TYPE_FLOAT64
		STRUCT_TYPE_BINARY
		STRUCT_TYPE_VEC8
		STRUCT_TYPE_VEC16
		STRUCT_TYPE_VEC32
		STRUCT_TYPE_VEC64
		STRUCT_TYPE_STRUCT
	]
	
	depth: 0											;-- used to trace nesting level for FORM/MOLD

	make-at: func [
		blk		[red-block!]
		size	[integer!]
		return: [red-block!]
	][
		if size < 0 [size: 1]
		
		blk/header: TYPE_BLOCK							;-- implicit reset of all header flags
		blk/head: 	0
		blk/node: 	alloc-cells size
		blk
	]

	make-in: func [
		parent	[red-block!]
		size 	[integer!]								;-- number of cells to pre-allocate
		return:	[red-block!]
		/local
			blk [red-block!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/make-in"]]
		
		blk: either null? parent [
			_root
		][
			assert any [
				TYPE_OF(parent) = TYPE_BLOCK			;@@ replace with ANY_BLOCK
				TYPE_OF(parent) = TYPE_PAREN
				TYPE_OF(parent) = TYPE_PATH
				TYPE_OF(parent) = TYPE_LIT_PATH
				TYPE_OF(parent) = TYPE_SET_PATH
				TYPE_OF(parent) = TYPE_GET_PATH
			]
			as red-block! ALLOC_TAIL(parent)
		]
		make-at blk size
	]
	
	push: func [
		blk [red-block!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/push"]]

		copy-cell as red-value! blk stack/push*
	]
	
	push*: func [
		size	[integer!]
		return: [red-block!]	
		/local
			blk [red-block!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/push*"]]
		
		blk: make-at as red-block! ALLOC_TAIL(root) size
		push blk
		blk
	]
		
	mold-each: func [
		blk		  [red-block!]
		buffer	  [red-string!]
		only?	  [logic!]
		all?	  [logic!]
		flat?	  [logic!]
		arg		  [red-value!]
		part 	  [integer!]
		indent	  [integer!]
		return:   [integer!]
		/local
			s	  [series!]
			head  [red-value!]
			tail  [red-value!]
			value [red-value!]
			lf?	  [logic!]
	][
		s: GET_BUFFER(blk)
		head:  s/offset + blk/head
		value: head
		tail:  s/tail
		
		lf?: off
		cycles/push blk/node
		
		while [value < tail][
			if all [OPTION?(arg) part <= 0][
				cycles/pop
				return part
			]
			depth: depth + 1
			unless cycles/detect? value buffer :part yes [
				unless flat? [
					if value/header and flag-new-line <> 0 [ ;-- new-line marker
						unless lf? [lf?: on indent: indent + 1]
						string/append-char GET_BUFFER(buffer) as-integer lf
						loop indent [string/concatenate-literal buffer "    "]
						part: part - (indent * 4 + 1) 		;-- account for lf
					]
				]
				part: actions/mold value buffer only? all? flat? arg part indent
			]
			if positive? depth [
				string/append-char GET_BUFFER(buffer) as-integer space
				part: part - 1
			]
			depth: depth - 1
			value: value + 1
		]
		cycles/pop
		
		s: GET_BUFFER(buffer)
		if value <> head [								;-- test if not empty block
			s/tail: as cell! (as byte-ptr! s/tail) - GET_UNIT(s) ;-- remove extra white space
			part: part + 1
		]
		if lf? [
			indent: indent - 1
			string/append-char GET_BUFFER(buffer) as-integer lf
			loop indent [string/concatenate-literal buffer "    "]
			part: part - (indent * 4 + 1) 		;-- account for lf
		]
		part
	]

	compare-each: func [
		blk1	   [red-block!]							;-- first operand
		blk2	   [red-block!]							;-- second operand
		op		   [integer!]							;-- type of comparison
		return:	   [integer!]
		/local
			s1	   [series!]
			s2	   [series!]
			size1  [integer!]
			size2  [integer!]
			type1  [integer!]
			type2  [integer!]
			value1 [red-value!]
			value2 [red-value!]
			res	   [integer!]
			n	   [integer!]
			len	   [integer!]
			same?  [logic!]
	][
		same?: all [
			blk1/node = blk2/node
			blk1/head = blk2/head
		]
		if op = COMP_SAME [return either same? [0][-1]]
		if all [
			same?
			any [op = COMP_EQUAL op = COMP_STRICT_EQUAL op = COMP_NOT_EQUAL]
		][return 0]

		s1: GET_BUFFER(blk1)
		s2: GET_BUFFER(blk2)
		size1: (as-integer s1/tail - s1/offset) >> 4 - blk1/head
		size2: (as-integer s2/tail - s2/offset) >> 4 - blk2/head

		if size1 <> size2 [										;-- shortcut exit for different sizes
			if any [
				op = COMP_EQUAL op = COMP_STRICT_EQUAL op = COMP_NOT_EQUAL
			][return 1]
		]

		if zero? size1 [return 0]								;-- shortcut exit for empty blocks

		value1: s1/offset + blk1/head
		value2: s2/offset + blk2/head
		len: either size1 < size2 [size1][size2]
		n: 0

		cycles/push blk1/node
		
		until [
			type1: TYPE_OF(value1)
			type2: TYPE_OF(value2)
			either any [
				type1 = type2
				all [word/any-word? type1 word/any-word? type2]
				all [											;@@ replace by ANY_NUMBER?
					any [type1 = TYPE_INTEGER type1 = TYPE_FLOAT]
					any [type2 = TYPE_INTEGER type2 = TYPE_FLOAT]
				]
			][
				either cycles/find? value1 [
					res: as-integer not natives/same? value1 value2
				][
					res: actions/compare-value value1 value2 op
				]
				value1: value1 + 1
				value2: value2 + 1
			][
				cycles/pop
				return SIGN_COMPARE_RESULT(type1 type2)
			]
			n: n + 1
			any [
				res <> 0
				n = len
			]
		]
		cycles/pop
		if zero? res [res: SIGN_COMPARE_RESULT(size1 size2)]
		res
	]

	;--- Actions ---
	
	make: func [
		proto	[red-block!]
		spec	[red-value!]
		type	[integer!]
		return:	[red-struct!]
		/local
			body	 [red-value!]
			values	 [red-value!]
			st		 [red-struct!]
			value	 [red-value!]
			tail	 [red-value!]
			blk		 [red-block!]
			word	 [red-word!]
			int		 [red-integer!]
			pi		 [int-ptr!]
			types	 [byte-ptr!]
			s		 [series!]
			len		 [integer!]
			sym		 [integer!]
			bits	 [integer!]
			type-len [integer!]
			
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/make"]]

		if any [
			TYPE_OF(spec) <> TYPE_BLOCK
			2 <> block/rs-length? as red-block! spec
		][
			0 ; error
		]
		spec: block/rs-head as red-block! spec
		body: spec + 1
		
		if TYPE_OF(spec) = TYPE_WORD [spec: _context/get as red-word! spec]
		if TYPE_OF(body) = TYPE_WORD [body: _context/get as red-word! body]
	
		if TYPE_OF(spec) <> TYPE_BLOCK [
			0 ; error
		]
		
		st: as red-struct! stack/push*
		st/header: TYPE_STRUCT
		blk: as red-block! spec
		st/spec: blk/node
		
		len: block/rs-length? blk
		
		switch TYPE_OF(body) [
			TYPE_BLOCK [
				if len <> block/rs-length? as red-block! body [
					0 ; error
				]
				values: block/rs-head as red-block! body
			]
			TYPE_NONE  [values: null]
			default    [
				0 ; error
			]
		]
		
		st/types: alloc-bytes 4 + len
		s: as series! st/types/value
		pi: as int-ptr! s/offset
		pi/value: len
		types: (as byte-ptr! s/offset) + 4
		
		s: GET_BUFFER(blk)
		value: s/offset + blk/head
		tail: s/tail
		
		while [value < tail][
			if TYPE_OF(value) <> TYPE_WORD [
				0 ; error
			]
			value: value + 1
			if TYPE_OF(value) <> TYPE_BLOCK [
				0 ; error
			]
			blk: as red-block! value
			word: as red-word! block/rs-head blk
			sym: symbol/resolve word/symbol
			
			type-len: block/rs-length? blk
			if any [type-len < 1 TYPE_OF(word) <> TYPE_WORD][
				0 ; error
			]
			word: word + 1
			bits: 0
			
			if all [type-len = 2 TYPE_OF(word) = TYPE_INTEGER][
				int: as red-integer! word
				bits: int/value
				unless any [bits = 8 bits = 16 bits = 32 bits = 64][
					0 ; error
				]
			]
			case [
				sym = words/char! [
					type: switch bits [
						0  [STRUCT_TYPE_CHAR32]
						8  [STRUCT_TYPE_CHAR8]
						16 [STRUCT_TYPE_CHAR16]
						32 [STRUCT_TYPE_CHAR32]
					]
				]
				sym = words/integer! [
					type: switch bits [
						0  [STRUCT_TYPE_INT32]
						8  [STRUCT_TYPE_INT8]
						16 [STRUCT_TYPE_INT16]
						32 [STRUCT_TYPE_INT32]
					]
				]
				sym = words/float! [
					type: either bits = 32 [STRUCT_TYPE_FLOAT32][STRUCT_TYPE_FLOAT64]
				]
				sym = words/binary! [
					type: STRUCT_TYPE_BINARY
				]
				sym = words/vector! [  ; [sub-type <bits>]
					0
				]
				sym = words/struct! [
					0
				]
			]
			types/value: as-byte type
			value: value + 1
		]
		st
	]

	;to: func [
	;	proto	[red-block!]
	;	spec	[red-value!]
	;	type	[integer!]
	;	return: [red-block!]
	;][
	;	#if debug? = yes [if verbose > 0 [print-line "struct/to"]]
	;
	;]

	form: func [
		blk		  [red-block!]
		buffer	  [red-string!]
		arg		  [red-value!]
		part 	  [integer!]
		return:   [integer!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/form"]]

		part
	]
	
	mold: func [
		blk		[red-block!]
		buffer	[red-string!]
		only?	[logic!]
		all?	[logic!]
		flat?	[logic!]
		arg		[red-value!]
		part	[integer!]
		indent	[integer!]
		return:	[integer!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/mold"]]
		
		part
	]
	
	compare: func [
		blk1	   [red-block!]							;-- first operand
		blk2	   [red-block!]							;-- second operand
		op		   [integer!]							;-- type of comparison
		return:	   [integer!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/compare"]]
		
		if TYPE_OF(blk2) <> TYPE_OF(blk1) [RETURN_COMPARE_OTHER]
		compare-each blk1 blk2 op
	]
	
	eval-path: func [
		parent	[red-block!]							;-- implicit type casting
		element	[red-value!]
		value	[red-value!]
		path	[red-value!]
		case?	[logic!]
		return:	[red-value!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/compare"]]
	]
	
	;--- Navigation actions ---
	
	find: func [
		blk			[red-block!]
		value		[red-value!]
		part		[red-value!]
		only?		[logic!]
		case?		[logic!]
		same?	 	[logic!]
		any?		[logic!]
		with-arg	[red-string!]
		skip		[red-integer!]
		last?		[logic!]
		reverse?	[logic!]
		tail?		[logic!]
		match?		[logic!]
		return:		[red-value!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/find"]]
		
		null
	]
	
	select: func [
		blk		 [red-block!]
		value	 [red-value!]
		part	 [red-value!]
		only?	 [logic!]
		case?	 [logic!]
		same?	 [logic!]
		any?	 [logic!]
		with-arg [red-string!]
		skip	 [red-integer!]
		last?	 [logic!]
		reverse? [logic!]
		return:	 [red-value!]
		/local
			s	   [series!]
			p	   [red-value!]
			b	   [red-block!]
			result [red-value!]
			type   [integer!]
			offset [integer!]
	][
		result: find blk value part only? case? same? any? with-arg skip last? reverse? no no
		
		if TYPE_OF(result) <> TYPE_NONE [
			offset: either only? [1][					;-- values > 0 => series comparison mode
				type: TYPE_OF(value)
				either ANY_BLOCK_STRICT?(type) [
					b: as red-block! value
					s: GET_BUFFER(b)
					(as-integer s/tail - s/offset) >> 4 - b/head
				][1]
			]
			blk: as red-block! result
			s: GET_BUFFER(blk)
			p: s/offset + blk/head + offset
			
			either p < s/tail [
				copy-cell p result
			][
				result/header: TYPE_NONE
			]
		]
		result
	]

	put: func [
		blk		[red-block!]
		field	[red-value!]
		value	[red-value!]
		case?	[logic!]
		return:	[red-value!]
		/local
			slot  [red-value!]
			s	  [series!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/put"]]
		
		blk: as red-block! find blk field null no case? no no null null no no no no
		
		either TYPE_OF(blk) = TYPE_NONE [
			copy-cell field ALLOC_TAIL(blk)
			copy-cell value ALLOC_TAIL(blk)
		][
			s: GET_BUFFER(blk)
			slot: s/offset + blk/head + 1
			if slot >= s/tail [slot: alloc-tail s]
			copy-cell value slot
			ownership/check as red-value! blk words/_put slot blk/head + 1 1
		]
		value
	]

	;--- Misc actions ---
	
	copy: func [
		blk	    	[red-block!]
		new			[red-block!]
		arg			[red-value!]
		deep?		[logic!]
		types		[red-value!]
		return:		[red-series!]
		/local
			s		[series!]
			type	[integer!]
	][
		#if debug? = yes [if verbose > 0 [print-line "struct/copy"]]

		new: as red-block! _series/copy as red-series! blk as red-series! new arg deep? types

		as red-series! new
	]

	init: does [
		datatype/register [
			TYPE_STRUCT
			TYPE_VALUE
			"struct!"
			;-- General actions --
			:make
			null			;random
			null			;reflect
			null			;to
			:form
			:mold
			:eval-path
			null			;set-path
			null			;compare
			;-- Scalar actions --
			null			;absolute
			null			;add
			null			;divide
			null			;multiply
			null			;negate
			null			;power
			null			;remainder
			null			;round
			null			;subtract
			null			;even?
			null			;odd?
			;-- Bitwise actions --
			null			;and~
			null			;complement
			null			;or~
			null			;xor~
			;-- Series actions --
			null			;append
			null			;at
			null			;back
			null			;change
			null			;clear
			null			;copy
			null			;find
			null			;head
			null			;head?
			null			;index?
			null			;insert
			null			;length?
			null			;move
			null			;next
			null			;pick
			null			;poke
			null			;put
			null			;remove
			null			;reverse
			null			;select
			null			;sort
			null			;skip
			null			;swap
			null			;tail
			null			;tail?
			null			;take
			null			;trim
			;-- I/O actions --
			null			;create
			null			;close
			null			;delete
			null			;modify
			null			;open
			null			;open?
			null			;query
			null			;read
			null			;rename
			null			;update
			null			;write
		]
	]
]
