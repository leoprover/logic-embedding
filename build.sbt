lazy val parserLib = ProjectRef(uri("git://github.com/leoprover/scala-tptp-parser#v1.2"), "tptpParser")

lazy val commonSettings = Seq(
  organization := "org.leo",
  scalaVersion := "2.13.5",
  scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
    ),
  licenses += "BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause")
)

lazy val embedding = (project in file("."))
  .disablePlugins(sbtassembly.AssemblyPlugin)
  .settings(
    commonSettings,
    version := "1.1",
    name := "logic-embedding",
    description := "A tool for embedding logics into higher-order logic",
  ).aggregate(runtime, app)

lazy val runtime = (project in file("embedding-runtime"))
	.settings(
	  commonSettings,
    name := "logic-embedding-runtime",
    version := "1.1",
    assemblyOption in assembly := (assemblyOption in assembly).value.copy(includeScala = false),
    test in assembly := {},
    assemblyJarName in assembly := s"${name.value}-${version.value}.jar",
	  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.5" % "test"
	).dependsOn(parserLib)

lazy val app = (project in file("embedding-app"))
	.settings(
	  commonSettings,
    name := "logic-embedding-app",
    version := "1.1",
    Compile/mainClass := Some("leo.modules.EmbeddingApp"),
    mainClass in assembly := Some("leo.modules.EmbeddingApp"),
    test in assembly := {},
    assemblyJarName in assembly := s"${name.value}-${version.value}.jar",
	  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.5" % "test"
	).dependsOn(runtime, parserLib)
