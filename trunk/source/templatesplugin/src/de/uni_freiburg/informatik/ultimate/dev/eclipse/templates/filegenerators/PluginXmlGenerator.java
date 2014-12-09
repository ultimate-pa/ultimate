package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;

public class PluginXmlGenerator
{
  protected static String nl;
  public static synchronized PluginXmlGenerator create(String lineSeparator)
  {
    nl = lineSeparator;
    PluginXmlGenerator result = new PluginXmlGenerator();
    nl = null;
    return result;
  }

  public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;
  protected final String TEXT_1 = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + NL + "<?eclipse version=\"3.2\"?>" + NL + "<plugin>" + NL + "\t<extension point=\"de.uni_freiburg.informatik.ultimate.ep.";
  protected final String TEXT_2 = "\">" + NL + "      <impl class=\"de.uni_freiburg.informatik.ultimate.plugins.";
  protected final String TEXT_3 = ".";
  protected final String TEXT_4 = ".";
  protected final String TEXT_5 = "\">" + NL + "      </impl>" + NL + "   </extension>" + NL + "</plugin>";
  protected final String TEXT_6 = NL;

  public String generate(Object argument)
  {
    final StringBuffer stringBuffer = new StringBuffer();
    
	UltimatePluginData data = (UltimatePluginData) argument; 

    stringBuffer.append(TEXT_1);
    stringBuffer.append(data.getTypeString());
    stringBuffer.append(TEXT_2);
    stringBuffer.append(data.getTypeString());
    stringBuffer.append(TEXT_3);
    stringBuffer.append(data.getPluginName().toLowerCase());
    stringBuffer.append(TEXT_4);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_5);
    stringBuffer.append(TEXT_6);
    return stringBuffer.toString();
  }
}
