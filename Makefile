DESTDIR ?= $(HOME)/bin
default: all

all: 
		@echo Building logic-embedding ...
		sbt assembly
		mkdir bin -p
		cp embedding-app/target/scala-3.9.0/logic-embedding-app-*.jar bin/.
		cat ./contrib/exec_dummy bin/logic-embedding-app-*.jar > bin/embedproblem
		chmod +x bin/embedproblem
		
native:
		sbt nativeImage
		cp embedding-app/target/native-image/logic-embedding-app bin/embedproblem-native
		chmod +x bin/embedproblem-native

install:
		install -m 0755 -d $(DESTDIR)
		install -m 0755 bin/embedproblem $(DESTDIR)

clean:
		rm -rf bin/
		rm -rf target/
		rm -rf embedding-app/target/
		rm -rf embedding-runtime/target/
