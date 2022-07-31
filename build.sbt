lazy val commonSettings = Seq(
  organization := "org.leo",
  version := "1.7.5",
  scalaVersion := "2.13.8",
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
    name := "logic-embedding",
    description := "A tool for embedding logics into higher-order logic",
  ).aggregate(runtime, app)

lazy val runtime = (project in file("embedding-runtime"))
	.settings(
	  commonSettings,
    name := "logic-embedding-runtime",
    assembly/assemblyOption := (assembly/assemblyOption).value.copy(includeScala = false),
    assembly/test := {},
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    unmanagedBase := baseDirectory.value / ".." / "lib",
    libraryDependencies += "io.github.leoprover" %% "scala-tptp-parser" % "1.6.4",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.12" % "test"
	)

lazy val app = (project in file("embedding-app"))
	.settings(
	  commonSettings,
    name := "logic-embedding-app",
    Compile/mainClass := Some("leo.modules.EmbeddingApp"),
    assembly/mainClass := Some("leo.modules.EmbeddingApp"),
    assembly/test := {},
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    unmanagedBase := baseDirectory.value / ".." / "lib",
    libraryDependencies += "io.github.leoprover" %% "scala-tptp-parser" % "1.6.4",
	  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.12" % "test"
	).dependsOn(runtime)
