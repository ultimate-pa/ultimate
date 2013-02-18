<?xml version="1.0" encoding="UTF-8"?>

<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<xsl:template match="filelist">
  <navi>
    <xsl:apply-templates />
  </navi>
</xsl:template>

<xsl:template match="file">
  <xsl:element name="subpage">
    <xsl:variable name="f" select="document(text())/page" />
    <xsl:copy-of select="$f/@id" />
    <xsl:copy-of select="$f/name" />
    <xsl:element name="link">
      <xsl:value-of select="concat(substring-before(text(), '.xml'), '.html')" />
    </xsl:element>
  </xsl:element>
</xsl:template>

</xsl:stylesheet>
