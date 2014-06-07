module IRTS.Java.Pom (pomString) where

import Data.List (unfoldr)
import Text.XML.Light

-----------------------------------------------------------------------
-- String <-> XML processing

uattr :: String -> String -> Attr
uattr k v = Attr (QName k Nothing Nothing) v

-- from http://stackoverflow.com/a/4978733/283260
splitOn :: Eq a => a -> [a] -> [[a]]
splitOn chr = unfoldr sep where
  sep [] = Nothing
  sep l  = Just . fmap (drop 1) . break (==chr) $ l

parseToDep :: String -> Element
parseToDep tuple =
  case splitOn ':' tuple of
    [g, a, v] -> dependency g a v
    _         -> blank_element

dependency :: String -> String -> String -> Element
dependency g a v = unode "dependency" (groupArtifactVersion g a v)

groupArtifactVersion :: String -> String -> String -> [Element]
groupArtifactVersion g a v = [
    unode "groupId" g,
    unode "artifactId" a,
    unode "version" v
  ]

pomString :: String -> String -> [String] -> String
pomString c a d = ppElement $ pom c a d

-----------------------------------------------------------------------
-- The pom template for idris projects

pom :: String -> String -> [String] -> Element
pom clsName artifactName dependencies = unode "project" ([
    uattr "xmlns" "http://maven.apache.org/POM/4.0.0",
    uattr "xmlns:xsi" "http://www.w3.org/2001/XMLSchema-instance",
    uattr "xsi:schemaLocation" "http://maven.apache.org/POM/4.0.0 http://maven.apache.org/maven-v4_0_0.xsd"
  ],
  [
    unode "modelVersion" "4.0.0",
    unode "groupId" "org.idris-lang",
    unode "artifactId" artifactName,
    unode "packaging" "jar",
    unode "version" "1.0",
    unode "name" artifactName,
    unode "properties" [
      unode "project.build.sourceEncoding" "UTF-8",
      unode "skipTest" "true"
    ],
    unode "dependencies" (
      dependency "org.idris-lang" "idris" "0.9.14" :
      map parseToDep dependencies
    ),
    unode "build" [
      unode "finalName" artifactName,
      unode "plugins" [
        unode "plugin" (
          unode "configuration" [
            unode "source" "1.7",
            unode "target" "1.7"
          ] : groupArtifactVersion "org.apache.maven.plugins" "maven-compiler-plugin" "3.0"
        ),
        unode "plugin" (
          unode "configuration" (
            unode "skipTests" "${skipTests}"
          ) : groupArtifactVersion "org.apache.maven.plugins" "maven-surefile-plugin" "2.14"
        ),
        unode "plugin" (
          unode "executions" [
            unode "execution" [
              unode "phase" "package",
              unode "goals" (
                unode "goal" "shade"
              ),
              unode "configuration" (
                unode "transformers" (
                  unode "transformer" (
                    uattr "implementation" "org.apache.maven.plugins.shade.resource.ManifestResourceTransformer",
                    unode "mainClass" clsName
                  )
                )
              )
            ]
          ] : groupArtifactVersion "org.apache.maven.plugins" "maven-shade-plugin" "2.1"
        )
      ]
    ]
  ])
