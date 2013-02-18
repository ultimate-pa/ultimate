package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;
import java.io.File;
import java.lang.reflect.Method;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.FileLocator;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class AutomataScriptInterpreterObserver implements IUnmanagedObserver {

	
	@Override
	public boolean process(IElement root) {
//		Map<String, Class<?>> test = getOperations();
		TestFileInterpreter ti = new TestFileInterpreter();
		try {
			ti.interpretTestFile((AtsASTNode)root);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return false;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	

	
	
	static private Map<String, Class<?>> getOperations() {
		Map<String, Class<?>> result = new HashMap<String, Class<?>>();
		String baseDir = "/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/operations";
		String[] dirs = { "", "buchiReduction" };
		for (String dir : dirs) {
			String[] files = filesInDirectory(baseDir + "/" + dir);
			for (String file : files) {
				if (file.endsWith(".class")) {
					String withoutSuffix = file.substring(0, file.length()-6);
					String path = baseDir + "." + withoutSuffix;
					Class<?> clazz = null;
					try {
						clazz = Class.forName(path);
					} catch (ClassNotFoundException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					if (true) {
						String operationName = withoutSuffix.toLowerCase();
						result.put(operationName, clazz);
					}
				}
			}
		}
		return result;
	}
	
	
	
	/**
	 * Return the filenames of the files in the folder
	 * /resources/examples/ + dirSuffix (path given relative to root of this
	 * package).
	 * 
	 * We use the classloader to get the URL of this folder. We support only
	 * URLs with protocol <i>file</i> and <i>bundleresource</i>.
	 * At the moment these are the only ones that occur in Website and
	 * WebsiteEclipseBridge.
	 */
	private static String[] filesInDirectory(String dir) {
		URL dirURL = IOperation.class.getClassLoader().getResource(dir);
		if (dirURL == null) {
			throw new UnsupportedOperationException("directory does not exist");
		}
		String protocol = dirURL.getProtocol();
		File dirFile = null;
		if (protocol.equals("file")) {
			try {
				dirFile = new File(dirURL.toURI());
			} catch (URISyntaxException e) {
				e.printStackTrace();
				throw new UnsupportedOperationException("directory does not exist");
			}
		} else if (protocol.equals("bundleresource")) {
			try {
				URL fileURL = FileLocator.toFileURL(dirURL);
				dirFile = new File(fileURL.toURI());
			} catch (Exception e) {
				e.printStackTrace();
				throw new UnsupportedOperationException("directory does not exist");
			}
		} else {
			throw new UnsupportedOperationException("unknown protocol");
		}
		String[] files = dirFile.list();
		return files;
	}
	
}
