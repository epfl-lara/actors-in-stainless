.PHONY: Counter

STAINLESS_ARGS := --debug=verification --timeout=20
BASE_FILES := src/main/scala/Actors.scala src/main/scala/CMap.scala
JAVA_ARGS := \
	-jar "../stainless/frontends/stainless-scalac-standalone/target/scala-2.12/stainless-scalac-standalone-0.1.0.jar" \
	-cp "$(HOME)/.ivy2/cache/com.typesafe.akka/akka-actor_2.12/jars/akka-actor_2.12-2.5.21.jar"

STAINLESS := java $(JAVA_ARGS) $(STAINLESS_ARGS) $(BASE_FILES)

Counter:
	 $(STAINLESS) src/main/scala/$@.scala
