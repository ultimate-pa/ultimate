package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;

public class ObserverGenerator
{
  protected static String nl;
  public static synchronized ObserverGenerator create(String lineSeparator)
  {
    nl = lineSeparator;
    ObserverGenerator result = new ObserverGenerator();
    nl = null;
    return result;
  }

  public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;
  protected final String TEXT_1 = "package de.uni_freiburg.informatik.ultimate.plugins.";
  protected final String TEXT_2 = ".";
  protected final String TEXT_3 = ";" + NL;
  protected final String TEXT_4 = "import de.uni_freiburg.informatik.ultimate.access.IManagedObserver;" + NL + "import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;" + NL + "import de.uni_freiburg.informatik.ultimate.access.WalkerOptions.Command;" + NL + "import de.uni_freiburg.informatik.ultimate.access.WalkerOptions.State;" + NL + "import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;" + NL + "import de.uni_freiburg.informatik.ultimate.model.IPayload;" + NL + "" + NL + "import org.apache.log4j.Logger;";
  protected final String TEXT_5 = "import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;" + NL + "import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;" + NL + "import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;" + NL + "import de.uni_freiburg.informatik.ultimate.model.IElement;" + NL + "" + NL + "import org.apache.log4j.Logger;";
  protected final String TEXT_6 = NL + NL + "/**" + NL + " * Auto-Generated Stub for the plug-in's Observer" + NL + " */" + NL + "public class ";
  protected final String TEXT_7 = "Observer implements ";
  protected final String TEXT_8 = "IManagedObserver";
  protected final String TEXT_9 = "IUnmanagedObserver";
  protected final String TEXT_10 = " {" + NL + "" + NL + "\tprivate static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);" + NL + "\t" + NL + "\t";
  protected final String TEXT_11 = "@Override" + NL + "\tpublic Command[] process(IPayload payload, State state, int childCount) {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t@Override" + NL + "\tpublic void finish() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\t" + NL + "\t}" + NL + "" + NL + "\t@Override" + NL + "\tpublic WalkerOptions getWalkerOptions() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t@Override" + NL + "\tpublic void init() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\t" + NL + "\t}" + NL + "" + NL + "\t@Override" + NL + "\tpublic boolean performedChanges() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn false;" + NL + "\t}";
  protected final String TEXT_12 = "@Override" + NL + "\tpublic boolean process(IElement root) {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn false;" + NL + "\t}" + NL + "" + NL + "\t@Override" + NL + "\tpublic void finish() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\t" + NL + "\t}" + NL + "" + NL + "\t@Override" + NL + "\tpublic WalkerOptions getWalkerOptions() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn null;" + NL + "\t}" + NL + "" + NL + "\t@Override" + NL + "\tpublic void init() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\t" + NL + "\t}" + NL + "" + NL + "\t@Override" + NL + "\tpublic boolean performedChanges() {" + NL + "\t\t// TODO Auto-generated method stub" + NL + "\t\treturn false;" + NL + "\t}";
  protected final String TEXT_13 = NL + NL + "}";
  protected final String TEXT_14 = NL;

  public String generate(Object argument)
  {
    final StringBuffer stringBuffer = new StringBuffer();
    
	UltimatePluginData data = (UltimatePluginData) argument; 

    stringBuffer.append(TEXT_1);
    stringBuffer.append(data.getTypeString());
    stringBuffer.append(TEXT_2);
    stringBuffer.append(data.getPluginName().toLowerCase());
    stringBuffer.append(TEXT_3);
    if(data.isManagedObserver()){
    stringBuffer.append(TEXT_4);
    }if(!data.isManagedObserver()){
    stringBuffer.append(TEXT_5);
    }
    stringBuffer.append(TEXT_6);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_7);
    if (data.isManagedObserver()){
    stringBuffer.append(TEXT_8);
    }else{
    stringBuffer.append(TEXT_9);
    }
    stringBuffer.append(TEXT_10);
    if(data.isManagedObserver()){
    stringBuffer.append(TEXT_11);
    }if(!data.isManagedObserver()){
	
	
    stringBuffer.append(TEXT_12);
    }
    stringBuffer.append(TEXT_13);
    stringBuffer.append(TEXT_14);
    return stringBuffer.toString();
  }
}
