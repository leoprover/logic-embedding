default: all

all: 
		@echo Building logic-embedding ...
		sbt assembly
		mkdir bin -p
		cp embedding-app/target/scala-2.13/logic-embedding-app-*.jar bin/.
		cat ./contrib/exec_dummy bin/logic-embedding-app-*.jar > bin/logic-embedding
		chmod +x bin/logic-embedding
