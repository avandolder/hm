val scala3Version = "3.0.0-RC3"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.2.0-RC2"

lazy val root = project
  .in(file("."))
  .settings(
    name := "scala3-simple",
    version := "0.1.0",

    scalaVersion := scala3Version,

    libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test",
  )
