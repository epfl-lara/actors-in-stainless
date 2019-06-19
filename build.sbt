
// lazy val `counter` = (project in file("."))
//   .enablePlugins(StainlessPlugin)
//   .settings(
//     name         := "stainless-actors-counter",
//     version      := "0.1.0",
//     scalaVersion := "2.12.8",

//     Compile/mainClass := Some("Counter"),

//     libraryDependencies ++= Seq(
//       "com.typesafe.akka" %% "akka-actor" % "2.5.21",
//     ),
//   )

lazy val `leaderElection` = (project in file("."))
  // .enablePlugins(StainlessPlugin)
  .settings(
    name         := "stainless-actors-leader-election",
    version      := "0.1.0",
    scalaVersion := "2.12.8",

    Compile/mainClass := Some("LeaderElection"),

    libraryDependencies ++= Seq(
      "com.typesafe.akka" %% "akka-actor" % "2.5.21",
    ),
  )

// lazy val `kvs` = (project in file("."))
//   .enablePlugins(StainlessPlugin)
//   .settings(
//     name         := "stainless-actors-kvs",
//     version      := "0.1.0",
//     scalaVersion := "2.12.8",

//     Compile/mainClass := Some("KVS"),

//     libraryDependencies ++= Seq(
//       "com.typesafe.akka" %% "akka-actor" % "2.5.21",
//     ),
//   )

// lazy val `counter2` = (project in file("."))
//   .enablePlugins(StainlessPlugin)
//   .settings(
//     name         := "stainless-actors-counter3",
//     version      := "0.1.0",
//     scalaVersion := "2.12.8",

//     Compile/mainClass := Some("ReplicatedCounter"),

//     libraryDependencies ++= Seq(
//       "com.typesafe.akka" %% "akka-actor" % "2.5.21",
//     ),
//   )

