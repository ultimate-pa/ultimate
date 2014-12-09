package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;

public class PluginClassGenerator
{
  protected static String nl;
  public static synchronized PluginClassGenerator create(String lineSeparator)
  {
    nl = lineSeparator;
    PluginClassGenerator result = new PluginClassGenerator();
    nl = null;
    return result;
  }

  public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;
  protected final String TEXT_1 = "package de.uni_freiburg.informatik.ultimate.plugins.";
  protected final String TEXT_2 = ".";
  protected final String TEXT_3 = ";" + NL + "" + NL + "import java.util.Collections;" + NL + "import java.util.List;" + NL + "" + NL + "import de.uni_freiburg.informatik.ultimate.access.IObserver;" + NL + "import de.uni_freiburg.informatik.ultimate.ep.interfaces.";
  protected final String TEXT_4 = ";" + NL + "import de.uni_freiburg.informatik.ultimate.model.GraphType;";
  protected final String TEXT_5 = NL + "import de.uni_freiburg.informatik.ultimate.model.IElement;";
  protected final String TEXT_6 = NL + "import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;" + NL + "import de.uni_freiburg.informatik.ultimate.model.TokenMap;" + NL + "import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;" + NL + "" + NL + "import org.apache.log4j.Logger;" + NL + "" + NL + "/**" + NL + " * Main class of Plug-In ";
  protected final String TEXT_7 = NL + " * " + NL + " *" + NL + " * TODO: refine comments" + NL + " * " + NL + " */" + NL + "public class ";
  protected final String TEXT_8 = " implements ";
  protected final String TEXT_9 = " {" + NL + "" + NL + "\tprivate static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;" + NL + "\tprivate static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;" + NL + "\t" + NL + "\tprivate ";
  protected final String TEXT_10 = "Observer m_Observer;" + NL + "\tprivate GraphType m_InputDefinition;" + NL + "\t" + NL + "\tprivate static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);" + NL + "\t" + NL + "\t";
  protected final String TEXT_11 = "/**" + NL + "\t* Keeps track of marked traces that should be visualized in a way." + NL + "\t*/" + NL + "\tprivate List<MarkedTrace> m_MarkedTraces;";
  protected final String TEXT_12 = NL + "\t" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()" + NL + "\t */" + NL + "\t@Override" + NL + "    public String getName() {" + NL + "        return s_PLUGIN_NAME;" + NL + "    }" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID()" + NL + "\t */" + NL + "\t@Override" + NL + "    public String getPluginID() {" + NL + "        return s_PLUGIN_ID;" + NL + "    }" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java.lang.Object)" + NL + "\t */" + NL + "\t@Override" + NL + "    public int init(Object param) {" + NL + "    \tm_Observer = new ";
  protected final String TEXT_13 = "Observer();" + NL + "    \treturn 0;" + NL + "    }" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getQueryKeyword()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic QueryKeyword getQueryKeyword() {" + NL + "\t\treturn ";
  protected final String TEXT_14 = ";" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getDesiredToolID()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic List<String> getDesiredToolID() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setTokenMap(de.uni_freiburg.informatik.ultimate.model.TokenMap)" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic void setTokenMap(TokenMap tokenMap) {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "" + NL + "\t}" + NL + "" + NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setInputDefinition(de.uni_freiburg.informatik.ultimate.model.GraphType)" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic void setInputDefinition(GraphType graphType) {" + NL + "\t\tthis.m_InputDefinition = graphType;" + NL + "\t}" + NL + "" + NL + "\t//@Override" + NL + "\tpublic List<IObserver> getObservers() {" + NL + "\t\treturn Collections.singletonList((IObserver) m_Observer);" + NL + "\t}" + NL + "\t";
  protected final String TEXT_15 = NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IModifyingTool#getOutputDefinition()" + NL + "\t */" + NL + "\tpublic GraphType getOutputDefinition() {" + NL + "\t\t/* " + NL + "\t\t * TODO This generated method body only assumes a standard case." + NL + "\t\t * Adapt it if necessary. Otherwise remove this todo-tag." + NL + "\t\t */" + NL + "\t\treturn new GraphType(Activator.s_PLUGIN_ID," + NL + "\t\t\t\tm_InputDefinition.getType(), m_InputDefinition.getFileNames());" + NL + "\t}" + NL + "\t";
  protected final String TEXT_16 = NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator#getModel()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic IElement getModel() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "\t";
  protected final String TEXT_17 = NL + "\t/* (non-Javadoc)" + NL + "\t * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getRequireGui()" + NL + "\t */" + NL + "\t@Override" + NL + "\tpublic boolean isGuiRequired() {" + NL + "\t\treturn ";
  protected final String TEXT_18 = ";" + NL + "\t}" + NL + "\t" + NL + "\t";
  protected final String TEXT_19 = "/**" + NL + "\t* Keeps track of marked traces that should be visualized in a way." + NL + "\t*/" + NL + "\tpublic void setMarkedTraces(List<MarkedTrace> traces){" + NL + "\t\tthis.m_MarkedTraces = traces;" + NL + "\t}";
  protected final String TEXT_20 = "/**" + NL + "\t* @return marked traces or null if no special markers shall be added for output plug-ins" + NL + "\t*/" + NL + "\tpublic List<MarkedTrace> getMarkedTraces(){" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}";
  protected final String TEXT_21 = NL + "}";
  protected final String TEXT_22 = NL;

  public String generate(Object argument)
  {
    final StringBuffer stringBuffer = new StringBuffer();
    
	UltimatePluginData data = (UltimatePluginData) argument; 

    stringBuffer.append(TEXT_1);
    stringBuffer.append(data.getTypeString());
    stringBuffer.append(TEXT_2);
    stringBuffer.append(data.getPluginName().toLowerCase());
    stringBuffer.append(TEXT_3);
    stringBuffer.append(data.getInterfaceName());
    stringBuffer.append(TEXT_4);
    if(data.getType() == UltimatePluginData.PluginType.generator){
    stringBuffer.append(TEXT_5);
    }
    stringBuffer.append(TEXT_6);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_7);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_8);
    stringBuffer.append(data.getInterfaceName());
    stringBuffer.append(TEXT_9);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_10);
     if(data.getType() == UltimatePluginData.PluginType.output){
    stringBuffer.append(TEXT_11);
    }
    stringBuffer.append(TEXT_12);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_13);
    stringBuffer.append(data.getQueryKeywordString());
    stringBuffer.append(TEXT_14);
    if(data.getType() == UltimatePluginData.PluginType.analysis || data.getType() == UltimatePluginData.PluginType.generator){
    stringBuffer.append(TEXT_15);
    if(data.getType() == UltimatePluginData.PluginType.generator){
    stringBuffer.append(TEXT_16);
    }}
    stringBuffer.append(TEXT_17);
    stringBuffer.append(data.isGuiRequired());
    stringBuffer.append(TEXT_18);
     if(data.getType() == UltimatePluginData.PluginType.output){
    stringBuffer.append(TEXT_19);
    } 
	else{
    stringBuffer.append(TEXT_20);
    }
    stringBuffer.append(TEXT_21);
    stringBuffer.append(TEXT_22);
    return stringBuffer.toString();
  }
}
