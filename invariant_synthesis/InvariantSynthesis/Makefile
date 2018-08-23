all: bin/InvariantSynthesis.exe

SRCS = \
	InvariantSynthesis_Linux/Config.fs \
	InvariantSynthesis/Helper.fs \
	InvariantSynthesis/AST.fs \
	InvariantSynthesis/MinimalAST.fs \
	InvariantSynthesis/Determinization.fs \
	InvariantSynthesis/Model.fs \
	InvariantSynthesis/InterpretedExpr.fs \
	InvariantSynthesis/Interpreter.fs \
	InvariantSynthesis/Trace.fs \
	InvariantSynthesis/TInterpreter.fs \
	InvariantSynthesis/WPR.fs \
	InvariantSynthesis/Printer.fs \
	InvariantSynthesis/Marking.fs \
	InvariantSynthesis/Formula.fs \
	InvariantSynthesis/Z3Utils.fs \
	InvariantSynthesis/Solver.fs \
	InvariantSynthesis/ConstraintsParser.fs \
	InvariantSynthesis/ParserAST.fs \
	InvariantSynthesis/TestModule.fs \
	InvariantSynthesis/AwesomeMinimize.fs \
	InvariantSynthesis/Program.fs


bin/InvariantSynthesis.exe: $(SRCS)
	fsharpc \
		-r:bin/Microsoft.Z3.dll \
		-r:bin/FParsec.dll \
		-r:bin/FParsecCS.dll \
		-r:bin/Prime.exe \
		-o bin/InvariantSynthesis.exe \
		$(SRCS)

parser: asdf
	cd Parser && make

asdf:
