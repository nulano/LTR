lazy val scalatest = "org.scalatest" %% "scalatest" % "3.2.15"

ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.1.3"

scalacOptions ++= Seq("-g:notailcalls")

lazy val root = (project in file("."))
  .settings(
    name := "check",
    libraryDependencies += scalatest % "it,test"
  )
