name := "mvpda-refinement"

version := "0.1"

scalaVersion := "2.10.0"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test"

antlrSettings

com.github.retronym.SbtOneJar.oneJarSettings

