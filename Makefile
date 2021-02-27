DESTDIR ?= $(HOME)/bin
default: all

all: 
		@echo Building logic-embedding ...
		sbt assembly
		mkdir bin -p
		cp embedding-app/target/scala-2.13/logic-embedding-app-*.jar bin/.
		cat ./contrib/exec_dummy bin/logic-embedding-app-*.jar > bin/embedproblem
		chmod +x bin/embedproblem

install:
		install -m 0755 -d $(DESTDIR)
		install -m 0755 bin/embedproblem $(DESTDIR)

clean:
		rm -rf bin/
		rm -rf target/
		rm -rf embedding-app/target/
		rm -rf embedding-runtime/target/
