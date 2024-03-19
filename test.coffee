y = 1 + 2 * 3
do () -> 
	1 + 2
	obj = ->
		test: true
	obj.test

x = 
	test: true
	testMethod: (x::int, y::int)::int ->
		x + y
	test2: false

a = ()::*wr.Request ->
	test: true