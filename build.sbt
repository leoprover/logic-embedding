lazy val commonSettings = Seq(
  organization := "org.leo",
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
    version := "1.6",
    name := "logic-embedding",
    description := "A tool for embedding logics into higher-order logic",
  ).aggregate(runtime, app)

lazy val runtime = (project in file("embedding-runtime"))
	.settings(
	  commonSettings,
    name := "logic-embedding-runtime",
    version := "1.4",
    assembly/assemblyOption := (assembly/assemblyOption).value.copy(includeScala = false),
    assembly/test := {},
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    unmanagedBase := baseDirectory.value / ".." / "lib",
    libraryDependencies += "io.github.leoprover" %% "scala-tptp-parser" % "1.5",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test"
	)

lazy val app = (project in file("embedding-app"))
	.settings(
	  commonSettings,
    name := "logic-embedding-app",
    version := "1.5",
    Compile/mainClass := Some("leo.modules.EmbeddingApp"),
    assembly/mainClass := Some("leo.modules.EmbeddingApp"),
    assembly/test := {},
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    unmanagedBase := baseDirectory.value / ".." / "lib",
    libraryDependencies += "io.github.leoprover" %% "scala-tptp-parser" % "1.5",
	  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test"
	).dependsOn(runtime)
