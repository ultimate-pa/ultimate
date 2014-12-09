package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators;

public class BuildPropertiesGenerator
{
  protected static String nl;
  public static synchronized BuildPropertiesGenerator create(String lineSeparator)
  {
    nl = lineSeparator;
    BuildPropertiesGenerator result = new BuildPropertiesGenerator();
    nl = null;
    return result;
  }

  public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;
  protected final String TEXT_1 = "source.. = src/" + NL + "output.. = bin/" + NL + "bin.includes = META-INF/,\\" + NL + "               .,\\" + NL + "               plugin.xml";
  protected final String TEXT_2 = NL;

  public String generate(Object argument)
  {
    final StringBuffer stringBuffer = new StringBuffer();
    stringBuffer.append(TEXT_1);
    stringBuffer.append(TEXT_2);
    return stringBuffer.toString();
  }
}
