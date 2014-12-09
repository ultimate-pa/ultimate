package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;

public class ManifestGenerator
{
  protected static String nl;
  public static synchronized ManifestGenerator create(String lineSeparator)
  {
    nl = lineSeparator;
    ManifestGenerator result = new ManifestGenerator();
    nl = null;
    return result;
  }

  public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;
  protected final String TEXT_1 = "Manifest-Version: 1.0" + NL + "Bundle-ManifestVersion: 2" + NL + "Bundle-Name: ";
  protected final String TEXT_2 = NL + "Bundle-SymbolicName: ";
  protected final String TEXT_3 = ";singleton:=true" + NL + "Bundle-Version: 1.0.0" + NL + "Bundle-Activator: de.uni_freiburg.informatik.ultimate.plugins.";
  protected final String TEXT_4 = ".";
  protected final String TEXT_5 = ".Activator" + NL + "Require-Bundle: org.eclipse.core.runtime," + NL + " UltimateCore" + NL + "Bundle-ActivationPolicy: lazy" + NL + "Bundle-RequiredExecutionEnvironment: JavaSE-1.6";
  protected final String TEXT_6 = NL;

  public String generate(Object argument)
  {
    final StringBuffer stringBuffer = new StringBuffer();
    
	UltimatePluginData data = (UltimatePluginData) argument; 

    stringBuffer.append(TEXT_1);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_2);
    stringBuffer.append(data.getPluginId());
    stringBuffer.append(TEXT_3);
    stringBuffer.append(data.getTypeString());
    stringBuffer.append(TEXT_4);
    stringBuffer.append(data.getPluginName().toLowerCase());
    stringBuffer.append(TEXT_5);
    stringBuffer.append(TEXT_6);
    return stringBuffer.toString();
  }
}
