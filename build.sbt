lazy val parserLib = ProjectRef(uri("git://github.com/leoprover/scala-tptp-parser#v1.1"), "tptpParser")

//ProjectRef(file("../scala-tptp-parser"), "tptpParser")
   // replace with GitHub link when possible: RootProject(uri("git://github.com/...#tagOrCommit"))

lazy val logicEmbedding = (project in file("."))
  .settings(
    name := "logic-embedding",
    description := "A tool for embedding logics into higher-order logic",
    version := "0.1",
    organization := "org.leo",
    scalaVersion := "2.13.4",
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
    ),
    licenses += "BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause"),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.2" % "test"
  ).dependsOn(parserLib)
