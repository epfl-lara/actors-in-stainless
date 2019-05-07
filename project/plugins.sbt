resolvers += Resolver.url(
  "LARA sbt plugins releases",
  url("https://dl.bintray.com/epfl-lara/sbt-plugins/")
)(Resolver.ivyStylePatterns)

addSbtPlugin("ch.epfl.lara" % "sbt-stainless" % "0.1.0-527e9e81d8c3f02ce4b579ed98ed7669209ce9e8")

