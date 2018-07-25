ARGS=""

all:
	dotnet build
	cp -n ../z3-4.6.0-x64-linux/bin/libz3.so ./bin/Debug/netcoreapp2.0/libz3.so
	cp -n ../Parser/_build/main.native ./bin/Debug/netcoreapp2.0/parser.native

test:
	cd ./bin/Debug/netcoreapp2.0/ ; dotnet InvariantSynthesis_Linux.dll ${ARGS}

clean:
	rm -r obj bin