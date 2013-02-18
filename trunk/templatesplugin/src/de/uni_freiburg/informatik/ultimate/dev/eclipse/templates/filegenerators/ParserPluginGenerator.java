package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;

public class ParserPluginGenerator
{
  protected static String nl;
  public static synchronized ParserPluginGenerator create(String lineSeparator)
  {
    nl = lineSeparator;
    ParserPluginGenerator result = new ParserPluginGenerator();
    nl = null;
    return result;
  }

  public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;
  protected final String TEXT_1 = "package de.uni_freiburg.informatik.ultimate.plugins.";
  protected final String TEXT_2 = ".";
  protected final String TEXT_3 = ";" + NL + "" + NL + "import java.io.File;" + NL + "" + NL + "import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;" + NL + "import de.uni_freiburg.informatik.ultimate.model.GraphType;" + NL + "import de.uni_freiburg.informatik.ultimate.model.INode;" + NL + "import de.uni_freiburg.informatik.ultimate.model.TokenMap;" + NL + "import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;" + NL + "" + NL + "import org.apache.log4j.Logger;" + NL + "" + NL + "public class ";
  protected final String TEXT_4 = " implements ISource {" + NL + "\t" + NL + "\tprotected String[] m_FileTypes = new String[] {";
  protected final String TEXT_5 = "};" + NL + "" + NL + "\tprivate static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);" + NL + "\t" + NL + "\t\t" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getFileTypes()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic String[] getFileTypes() {" + NL + "        return m_FileTypes;" + NL + "    }" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getOutputDefinition()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic GraphType getOutputDefinition() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getTokenMap()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic TokenMap getTokenMap() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getTokens()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic String[] getTokens() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseAST(java.io.File[])" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic INode parseAST(File[] files) throws Exception {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseAST(java.io.File)" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic INode parseAST(File file) throws Exception {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseable(java.io.File)" + NL + "\t */" + NL + "\t@Override" + NL + "    public boolean parseable(File[] files) {" + NL + "        for (File f : files) {" + NL + "            if (!parseable(f)) { return false; }" + NL + "        }" + NL + "        return true;" + NL + "    }" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseable(java.io.File)" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic boolean parseable(File file) {" + NL + "\t\tfor(String s : getFileTypes())" + NL + "    \t{" + NL + "    \t\tif(file.getName().endsWith(s))" + NL + "    \t\t\treturn true;" + NL + "    \t}" + NL + "        return false;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#setPreludeFile(java.io.File)" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic void setPreludeFile(File prelude) {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic String getName() {" + NL + "\t\treturn Activator.s_PLUGIN_NAME;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic String getPluginID() {" + NL + "\t\treturn Activator.s_PLUGIN_ID;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java.lang.Object)" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic int init(Object params) {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn 0;" + NL + "\t}" + NL + "" + NL + "}";
  protected final String TEXT_6 = NL;

  public String generate(Object argument)
  {
    final StringBuffer stringBuffer = new StringBuffer();
    
	UltimatePluginData data = (UltimatePluginData) argument; 

    stringBuffer.append(TEXT_1);
    stringBuffer.append(data.getTypeString());
    stringBuffer.append(TEXT_2);
    stringBuffer.append(data.getPluginName().toLowerCase());
    stringBuffer.append(TEXT_3);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_4);
    stringBuffer.append(data.getCommaSepFileTypeStrings());
    stringBuffer.append(TEXT_5);
    stringBuffer.append(TEXT_6);
    return stringBuffer.toString();
  }
}
