check:
	ivy_check queue_epr.ivy
test:
	ivy_to_cpp target=repl isolate=iso_impl queue_epr.ivy
	g++ -pthread -g -o queue_epr queue_epr.cpp
	./queue_epr
