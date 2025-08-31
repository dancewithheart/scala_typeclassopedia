// sbt dependencyBrowseTree
addDependencyTreePlugin
// sbt dependencyUpdates
addSbtPlugin("com.timushev.sbt"          % "sbt-updates"   % "0.6.4")
//addSbtPlugin("org.typelevel"             % "sbt-tpolecat"  % "0.5.2")
// sbt scalafmtAll
addSbtPlugin("org.scalameta"             % "sbt-scalafmt"  % "2.5.5")
// sbt clean coverage test coverageReport
addSbtPlugin("org.scoverage"             % "sbt-scoverage" % "2.3.1")
