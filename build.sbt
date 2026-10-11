lazy val commonSettings = Seq(
  organization := "org.leo",
  version := "1.9.6",
  scalaVersion := "2.13.18",
  scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
    ),
  licenses += "BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause"),

  libraryDependencies += "io.github.leoprover" %% "scala-tptp-parser" % "1.7.5",
  libraryDependencies += "io.github.leoprover" %% "tptp-utils-runtime" % "1.5.0",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.20" % "test"
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
	)

lazy val app = (project in file("embedding-app"))
  .enablePlugins(NativeImagePlugin)
	.settings(
	  commonSettings,
    name := "logic-embedding-app",
    Compile/mainClass := Some("leo.modules.EmbeddingApp"),
    assembly/mainClass := Some("leo.modules.EmbeddingApp"),
    assembly/test := {},
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    nativeImageOptions += s"-H:ReflectionConfigurationFiles=${baseDirectory.value / ".." / "contrib" / "native-image-configs" / "reflect-config.json"}",
    nativeImageOptions += s"-H:ConfigurationFileDirectories=${baseDirectory.value / ".."  / "contrib" / "native-image-configs" }",
    nativeImageOptions +="-H:+JNI",
	).dependsOn(runtime)
