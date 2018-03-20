check:
	ivy_check verdi_lock4.ivy
test:
	ivy_to_cpp target=repl isolate=iso_impl verdi_lock4.ivy
	g++ -pthread -g -o verdi_lock verdi_lock4.cpp
	./verdi_lock
