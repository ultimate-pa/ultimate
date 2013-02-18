package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;

public class ActivatorGenerator
{
  protected static String nl;
  public static synchronized ActivatorGenerator create(String lineSeparator)
  {
    nl = lineSeparator;
    ActivatorGenerator result = new ActivatorGenerator();
    nl = null;
    return result;
  }

  public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;
  protected final String TEXT_1 = "package de.uni_freiburg.informatik.ultimate.plugins.";
  protected final String TEXT_2 = ".";
  protected final String TEXT_3 = ";" + NL + "" + NL + "import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;" + NL + "" + NL + "import org.eclipse.core.runtime.Plugin;" + NL + "import org.osgi.framework.BundleContext;" + NL + "import org.apache.log4j.Logger;" + NL + "" + NL + "" + NL + "/**" + NL + " * The activator class controls the plug-in life cycle" + NL + " */" + NL + "public class Activator extends Plugin {" + NL + "" + NL + "\t// The plug-in ID" + NL + "\tpublic static final String s_PLUGIN_ID = \"";
  protected final String TEXT_4 = "\";" + NL + "" + NL + "\t// The plug-in name" + NL + "\tpublic static final String s_PLUGIN_NAME = \"";
  protected final String TEXT_5 = "\";" + NL + "\t// The shared instance" + NL + "\tprivate static Activator m_Plugin;" + NL + "\t" + NL + "\tprivate static Logger s_Logger = UltimateServices.getInstance().getLogger(s_PLUGIN_ID);" + NL + "\t" + NL + "\t/**" + NL + "\t * The constructor" + NL + "\t */" + NL + "\tpublic Activator() {" + NL + "\t}" + NL + "" + NL + "\t/*" + NL + "\t * (non-Javadoc)" + NL + "\t * @see org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)" + NL + "\t */" + NL + "\tpublic void start(BundleContext context) throws Exception {" + NL + "\t\tsuper.start(context);" + NL + "\t\tm_Plugin = this;" + NL + "\t}" + NL + "" + NL + "\t/*" + NL + "\t * (non-Javadoc)" + NL + "\t * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)" + NL + "\t */" + NL + "\tpublic void stop(BundleContext context) throws Exception {" + NL + "\t\tm_Plugin = null;" + NL + "\t\tsuper.stop(context);" + NL + "\t}" + NL + "" + NL + "\t/**" + NL + "\t * Returns the shared instance" + NL + "\t *" + NL + "\t * @return the shared instance" + NL + "\t */" + NL + "\tpublic static Activator getDefault() {" + NL + "\t\treturn m_Plugin;" + NL + "\t}" + NL + "" + NL + "}";
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
    stringBuffer.append(data.getPluginId());
    stringBuffer.append(TEXT_4);
    stringBuffer.append(data.getPluginName());
    stringBuffer.append(TEXT_5);
    stringBuffer.append(TEXT_6);
    return stringBuffer.toString();
  }
}
