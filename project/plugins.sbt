resolvers += Resolver.url(
  "LARA sbt plugins releases",
  url("https://dl.bintray.com/epfl-lara/sbt-plugins/")
)(Resolver.ivyStylePatterns)

addSbtPlugin("ch.epfl.lara" % "sbt-stainless" % "0.1.0-9a4514350534c4bacc803598230bdc8286b26385")

