val scala2 = "2.13.18"
val scala3 = "3.9.0"

lazy val commonSettings = Seq(
  organization := "io.github.leoprover",
  homepage := Some(url("https://github.com/leoprover/logic-embedding")),
  scmInfo := Some(ScmInfo(
    browseUrl = url("https://github.com/leoprover/logic-embedding"),
    connection = "scm:git:git@github.com:leoprover/logic-embedding.git"
  )),
  developers := List(
    Developer(
      "lex-lex",
      "Alexander Steen",
      "alx.steen@gmail.com",
      url("https://www.alexandersteen.de/")
    )
  ),
  licenses += "BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause"),

  crossScalaVersions := Seq(scala2) ++ Seq(scala3),
  scalaVersion := crossScalaVersions.value.head,
  scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
    ),

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
    publish / skip := true // don't publish the root project
  ).aggregate(runtime, app)

lazy val runtime = (project in file("embedding-runtime"))
	.settings(
	  commonSettings,
    name := "logic-embedding-runtime",
    description :=
      """The tool translates a TPTP problem statement formulated in a non-classical logic
        | (using the logic specification format) into classical higher-order logic (THF format) or
        | first-order logic (TFF format), either using monomorphic or polymorphic types.""".stripMargin,
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
    publish / skip := true
	).dependsOn(runtime)
