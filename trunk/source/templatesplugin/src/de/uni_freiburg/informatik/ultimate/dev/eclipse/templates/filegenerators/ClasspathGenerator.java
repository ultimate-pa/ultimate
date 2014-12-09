package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators;

public class ClasspathGenerator
{
  protected static String nl;
  public static synchronized ClasspathGenerator create(String lineSeparator)
  {
    nl = lineSeparator;
    ClasspathGenerator result = new ClasspathGenerator();
    nl = null;
    return result;
  }

  public final String NL = nl == null ? (System.getProperties().getProperty("line.separator")) : nl;
  protected final String TEXT_1 = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + NL + "<classpath>" + NL + "\t<classpathentry kind=\"con\" path=\"org.eclipse.jdt.launching.JRE_CONTAINER/org.eclipse.jdt.internal.debug.ui.launcher.StandardVMType/JavaSE-1.6\"/>" + NL + "\t<classpathentry exported=\"true\" kind=\"con\" path=\"org.eclipse.pde.core.requiredPlugins\"/>" + NL + "\t<classpathentry kind=\"src\" path=\"src\"/>" + NL + "\t<classpathentry kind=\"output\" path=\"bin\"/>" + NL + "</classpath>";
  protected final String TEXT_2 = NL;

  public String generate(Object argument)
  {
    final StringBuffer stringBuffer = new StringBuffer();
    stringBuffer.append(TEXT_1);
    stringBuffer.append(TEXT_2);
    return stringBuffer.toString();
  }
}
