lazy val commonSettings = Seq(
  organization := "org.leo",
  version := "1.7.8",
  scalaVersion := "2.13.10",
  scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
    ),
  licenses += "BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause"),
  resolvers += "Sonatype S01 OSS Snapshots" at "https://s01.oss.sonatype.org/content/repositories/snapshots",

  libraryDependencies += "io.github.leoprover" %% "scala-tptp-parser" % "1.6.5+7-f3855f3f-SNAPSHOT",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.15" % "test"
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
    assembly / assemblyOption ~= {
      _.withIncludeScala(false)
    },
    assembly/test := {},
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    unmanagedBase := baseDirectory.value / ".." / "lib"
	)

lazy val app = (project in file("embedding-app"))
	.settings(
	  commonSettings,
    name := "logic-embedding-app",
    Compile/mainClass := Some("leo.modules.EmbeddingApp"),
    assembly/mainClass := Some("leo.modules.EmbeddingApp"),
    assembly/test := {},
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    unmanagedBase := baseDirectory.value / ".." / "lib"
	).dependsOn(runtime)
