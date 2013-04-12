
resolvers += "stefri" at "http://stefri.github.com/repo/snapshots"

addSbtPlugin("com.github.stefri" % "sbt-antlr" % "0.4-SNAPSHOT")

resolvers += Resolver.url(
  "sbt-plugin-releases", 
  new URL("http://scalasbt.artifactoryonline.com/scalasbt/sbt-plugin-releases/")
)(Resolver.ivyStylePatterns)

addSbtPlugin("com.github.retronym" % "sbt-onejar" % "0.8")
