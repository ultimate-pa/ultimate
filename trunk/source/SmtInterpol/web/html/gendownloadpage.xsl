<?xml version="1.0" encoding="UTF-8"?>

<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:output
      method = "xml"
      encoding = "UTF-8"
      omit-xml-declaration = "no"
      indent = "yes" />

  <xsl:template match="/">
    <page id="download">
      <name>Download</name>
      <content>
	<head1>License</head1>
	<txt>This program is free software; you can redistribute it and/or modify
	it under the terms of the <link
	url="http://www.gnu.org/licenses/lgpl.html">GNU Lesser General Public
	License</link> as published by the Free Software Foundation; either
	version 3 of the License, or (at your option) any later version.</txt>
	
	<txt>This program is distributed in the hope that it will be useful, but
	WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
	or FITNESS FOR A PARTICULAR PURPOSE. See the <link
	url="http://www.gnu.org/licenses/lgpl.html">GNU Lesser General Public
	License</link> for more details.</txt>
	<head1>Downloads</head1>
	<txt>We provide precompiled JARs and source ZIPs.  The source ZIPs also contain the source for some samples.</txt>
	<table>
	  <headrow>
	    <col>Description</col>
	    <col>Binary</col>
	  </headrow>
	  <row>
	    <col>Precompiled binary (version 2.0 revision <xsl:value-of select="//entry/@revision" />qb)</col>
	    <col><link url="smtinterpol.jar">smtinterpol.jar</link><nl />(Checksums: <link url="smtinterpol.jar.md5">MD5</link>, <link url="smtinterpol.jar.sha">SHA 256</link>)</col>
	  </row>
	  <row>
	    <col>Sources (version 2.0 revision <xsl:value-of select="//entry/@revision" />qb)</col>
	    <col><link url="smtinterpol-src.zip">smtinterpol-src.zip</link><nl />(Checksums: <link url="smtinterpol-src.zip.md5">MD5</link>, <link url="smtinterpol-src.zip.sha">SHA 256</link>)</col>
	  </row>
	</table>
      </content>
    </page>
  </xsl:template>
</xsl:stylesheet>
