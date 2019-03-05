
lazy val `root` = (project in file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name         := "stainless-actors",
    version      := "0.1.0",
    scalaVersion := "2.11.12",
    mainClass    := Some("Main"),
    libraryDependencies ++= Seq(
      "com.typesafe.akka" %% "akka-actor" % "2.5.21"
    )
  )

