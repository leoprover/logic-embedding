lazy val parserLib = ProjectRef(uri("git://github.com/leoprover/scala-tptp-parser#v1.2"), "tptpParser")

lazy val commonSettings = Seq(
  version := "0.1",
  organization := "org.leo",
  scalaVersion := "2.13.4",
  scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
    ),
  licenses += "BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause")
)

lazy val embedding = (project in file("."))
  .settings(
    commonSettings,
    name := "logic-embedding",
    description := "A tool for embedding logics into higher-order logic"
  ).aggregate(runtime, app)

lazy val runtime = (project in file("embedding-runtime"))
	.settings(
	  commonSettings,
    name := "logic-embedding-runtime",
	  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.2" % "test"
	).dependsOn(parserLib)

lazy val app = (project in file("embedding-app"))
	.settings(
	  commonSettings,
    name := "logic-embedding-app",
    Compile/mainClass := Some("leo.modules.EmbeddingApp"),
	  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.2" % "test"
	).dependsOn(runtime)

