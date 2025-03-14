package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Random;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

import org.osgi.framework.Bundle;
import org.osgi.framework.wiring.BundleWiring;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.ICFGExecuterPreferences;

public class DynamicLoader {
	private final static String packageName = IcfgInterpreter.class.getPackageName();
	private final static String[] packageParts = packageName.split("[.]");
	private final static String packagePath = connectPath(packageParts);

	private final static String projectPath = ICFGExecuterPreferences.getProjectSourceDirectory().getAbsolutePath();

	private final static String outputFolder = connectPath("compiler", "ICFG_Out");

	private static final String seperatorRegex = "[" + File.separator + File.separator + "]";

	private static String connectPath(final String... parts) {
		return String.join(File.separator, parts);
	}

	/**
	 * Returns the base package expected for a {@link MainCompileFile} <br>
	 * It is allowed to append to the package, like: ...compiler.ICFG_Out{@code .example.extended.package}
	 */
	public static String getOutPackage() {
		return packageName + "." + outputFolder.replaceAll(seperatorRegex, ".");
	}

	private static class WrongFileExtensionException extends IOException {
		private static final long serialVersionUID = 654321L;

		public WrongFileExtensionException(final String message) {
			super(message);
		}
	}

	/**
	 * Used to ensure that the File to be compiled was created by the appropriate Method and is inside the appropriate
	 * folder. public static class MainCompileFile extends File { private static final long serialVersionUID = 123456L;
	 * /** de/uni_freiburg/informatik/ultimate/plugins/cfgexecuter/compiler/ICFG_Out * / private static final Path
	 * mainClassPath = new File(connectPath(packagePath, outputFolder)).toPath(); public MainCompileFile(String
	 * pathname) { super(pathname); assert this.toPath().startsWith(mainClassPath); } }
	 */

	/**
	 * Creates a .java File object for compilation and loading via {@link #loadClass(File, ArrayList, String)} <br>
	 * The class' package should begin as indicated by {@link #getOutPackage()} <br>
	 * It should extend some interface. That interface will be used by {@link #loadClass(File, ArrayList, String)} to
	 * create instances of this class.
	 *
	 * @param mCode     The plain-text code to be written to the returned .java File
	 * @param className The simple name of the class
	 * @return The .java File in the folder used for compilation
	 */
	public static File createFile(final String mCode, final String className) throws IOException {
		final File codeFile = new /* MainCompile */File(className + ".java");
		codeFile.getParentFile().mkdirs();

		final FileWriter writer = new FileWriter(codeFile);
		writer.write(mCode);
		writer.flush();
		writer.close();

		return codeFile;
	}

	/**
	 * Creates a .java File object for compilation and loading via {@link #loadClass(File, ArrayList, String)} <br>
	 * The class' package should begin as indicated by {@link #getOutPackage()} <br>
	 * It should extend some interface. That interface will be used by {@link #loadClass(File, ArrayList, String)} to
	 * create instances of this class.
	 *
	 * @param sourceFile The .java File that contains the code of the class that should be compiled.
	 * @return The .java File in the folder used for compilation
	 */
	public static File createFile(final File sourceFile, final String className) throws IOException {
		if (!sourceFile.exists()) {
			throw new FileNotFoundException();
		}
		if (!sourceFile.getName().endsWith(".java")) {
			throw new WrongFileExtensionException(sourceFile.toString() + " is not a .java File");
		}
		final File codeFile = new File(className + ".java");
		codeFile.getParentFile().mkdirs();
		Files.copy(sourceFile.toPath(), codeFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
		return codeFile;
	}

	/**
	 * Gets a .java File object for a class inside this plug-ins package. The File points to a copy, not the original.
	 * <br>
	 * The class' package needs to start with de.uni_freiburg.informatik.ultimate.plugins.cfgexecuter
	 *
	 * @param className The name of a class that is imported, relative to the plug-in base package. <br>
	 *                  This class ({@link DynamicLoader}) would be opened with
	 *                  openPluginClassFile("compiler/DynamicLoader")
	 * @return A file pointing to a copy of the .java source file of the given class
	 */
	public static File openPluginClassFile(final String className) throws IOException {
		final File originalFile = new File(connectPath(projectPath, "src", packagePath, className + ".java"));
		final File tempFile = new File(connectPath(packagePath, className + ".java"));
		tempFile.getParentFile().mkdirs();
		Files.copy(originalFile.toPath(), tempFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
		return tempFile;
	}

	/**
	 * Creates a copy of a .java File object for a class outside this plug-ins package. <br>
	 * The copy is created in the same directory as those made by {@link #openPluginClassFile(String)}, used for
	 * compilation.
	 *
	 * @param sourceFile File containing a class that is imported.
	 * @param className  The class' name, including the full package. For example: <br>
	 *                   {@code package example.package.name; public class MyClass...} <br>
	 *                   => className = "exmaple/package/name/MyClass"
	 * @return A file pointing to a copy of the .java source file of the given class
	 */
	public static File openOutsideClassFile(final File sourceFile, final String className) throws IOException {
		if (!sourceFile.exists()) {
			throw new FileNotFoundException(
					"Couldn't find file " + sourceFile.getAbsolutePath() + " of class " + className);
		}
		if (!sourceFile.getName().endsWith(".java")) {
			throw new WrongFileExtensionException(sourceFile.toString() + " is not a .java File");
		}
		final File tempFile = new File(connectPath(packagePath, className + ".java"));
		tempFile.getParentFile().mkdirs();
		Files.copy(sourceFile.toPath(), tempFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
		return tempFile;
	}

	private static File copyToBin(final File compiledFile, final String className) throws IOException {
		final File loadableFile = new File(connectPath(projectPath, "bin", className + ".class"));
		System.out.println(loadableFile);
		loadableFile.getParentFile().mkdirs();
		Files.copy(compiledFile.toPath(), loadableFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
		return loadableFile;
	}

	public static File compileClass(final File mainFile, final String className, final ArrayList<File> importFiles)
			throws ClassCastException, IOException {
		System.out.println("Non-Java imports:");
		for (final File f : importFiles) {
			System.out.println(f);
		}
		if (!importFiles.contains(mainFile)) {
			importFiles.add(mainFile);
		}

		final DiagnosticCollector<JavaFileObject> diagnosticListener = new DiagnosticCollector<>();
		final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
		final StandardJavaFileManager fileManager = compiler.getStandardFileManager(diagnosticListener, null, null);

		final Iterable<? extends JavaFileObject> compilationUnits = fileManager
				.getJavaFileObjectsFromFiles(importFiles);

		final JavaCompiler.CompilationTask task = compiler.getTask(null, fileManager, diagnosticListener, null, null,
				compilationUnits);

		final boolean success = task.call();
		fileManager.close();

		importFiles.remove(mainFile);

		if (!success) {
			System.out.println("Encountered failure while compiling.");
			for (final Diagnostic<? extends JavaFileObject> diagnostic : diagnosticListener.getDiagnostics()) {
				System.out.println("\nError on line " + diagnostic.getLineNumber());
				final String message = diagnostic.getMessage(null);
				if (!message.contains("cannot find symbol")) {
					System.out.println(message);
					continue;
				}
				final String classAndLoc = message.split("symbol:   class ")[1];
				final String[] parts = classAndLoc.split("\n  location: ");
				if (parts.length != 2) {
					System.out.println(message);
					continue;
				}
				System.out.println("The class \"" + parts[0] + "\" may not be imported. It is required by " + parts[1]);
			}
			return null;
		}
		System.out.println("File compiled soccessfully.");

		final File compiledFile = new File(className + ".class");
		return copyToBin(compiledFile, className);
	}

	/**
	 * TODO Compiles the given files and creates a {@link LoadedClass} object. <br>
	 * Usage: <br>
	 * {@code LoadedClass loadedClass = DynamicLoader.loadClass(main, imports, name);} <br>
	 * {@code InterfaceClass instance = loadedClass.createInstance(InterfaceClass.class, paramTypes, paramValues);}
	 *
	 * @param mainFile    .java file that contains the class to be loaded. This class should extend some interface such
	 *                    that <br>
	 *                    (Obtained via {@link #createFile(File)} or {@link #createFile(String, String)}
	 * @param className   Name of the target class in <strong>mainFile</strong>.
	 * @param importFiles List of .java files that are imported by either <strong>classFile</strong> or any file of
	 *                    <strong>importFiles</strong>. <br>
	 *                    (Obtained via {@link #openPluginClassFile(String)} or {@link #openOutsideClassFile(File)})
	 * @return A {@link LoadedClass} that can create instances of the target class as objects of the interface.
	 */
	public static LoadedClass loadClass(final File mainFile, final String className, final ArrayList<File> importFiles)
			throws ClassNotFoundException, ClassCastException, IOException {
		final File compiledFile = compileClass(mainFile, className, importFiles);

		final Activator act = Activator.getInstance();
		final Bundle bundle = act.getBundle();
		final BundleWiring bundleW = bundle.adapt(BundleWiring.class);
		final ClassLoader cl = bundleW.getClassLoader();

		final Class<?> loadedClass = cl.loadClass(className.replaceAll(seperatorRegex, "."));

		return new LoadedClass(className, mainFile, compiledFile, importFiles, loadedClass);
	}

	/**
	 * This object represents a class compiled and loaded at runtime using
	 * {@link DynamicLoader#loadClass(MainCompileFile, String, ArrayList)}. <br>
	 * It can encode itself in a String using {@link #encodeClassData()}. <br>
	 * That String can be used to recreate the {@link LoadedClass} later by using {@link #restoreClassData(String)}
	 */
	public static class LoadedClass {
		public final String className;
		private final File sourceFile;
		private final File compiledFile;
		private final ArrayList<File> imports;
		private final Class<?> classData;

		private LoadedClass(final String mClassName, final File mSourceFile, final File mCompiledFile,
				final ArrayList<File> mImports, final Class<?> mClassData) {
			imports = mImports;
			sourceFile = mSourceFile;
			compiledFile = mCompiledFile;
			className = mClassName;
			classData = mClassData;
		}

		/**
		 * Creates an instance of the class.
		 *
		 * @param <T>            The interface. (The class loaded in this {@link LoadedClass} has to extend that
		 *                       interface)
		 * @param castInterface  The interface to cast to (e.g. MyInterface.class)
		 * @param parameterTypes The classes of the constructor parameters. <br>
		 *                       MyClass(String a, int b) => <code>new Class<?>[] {String.class, int.class};</code>
		 * @param initargs       The values of the constructor parameters. <br>
		 *                       MyClass(String a, int b) => <code>new Object[] {a, b};</code>
		 * @return An instance of the class
		 */
		public <T> T createInstance(final Class<T> castInterface, final Class<?>[] parameterTypes,
				final Object[] initargs)
				throws InstantiationException, IllegalAccessException, IllegalArgumentException,
				InvocationTargetException, NoSuchMethodException, SecurityException, ClassCastException {
			return castInstance(createInstanceUncast(parameterTypes, initargs), castInterface);
		}

		/**
		 * Takes an object and a class or interface and casts the object to that class / interface.
		 *
		 * @param <T>           The interface. (The object has to extend that interface / be an instance of that class)
		 * @param instance      An object
		 * @param castInterface The interface to cast to (e.g. MyInterface.class)
		 * @return An instance of the class
		 */
		public static <T> T castInstance(final Object instance, final Class<T> castInterface)
				throws ClassCastException {
			if (castInterface.isInstance(instance)) {
				return castInterface.cast(instance);
			}
			throw new ClassCastException(
					"The object " + instance.toString() + " of class " + instance.getClass().getName()
							+ " is not / does not implement the class " + castInterface.getName() + ".");
		}

		/**
		 * Creates an instance of the class without casting it to a specific class.<br>
		 * This may be used to cast an object to multiple interfaces to access all its methods.
		 *
		 * @param parameterTypes The classes of the constructor parameters. <br>
		 *                       MyClass(String a, int b) => <code>new Class<?>[] {String.class, int.class};</code>
		 * @param initargs       The values of the constructor parameters. <br>
		 *                       MyClass(String a, int b) => <code>new Object[] {a, b};</code>
		 * @return An object which is an instance of
		 */
		public Object createInstanceUncast(final Class<?>[] parameterTypes, final Object[] initargs)
				throws InstantiationException, IllegalAccessException, IllegalArgumentException,
				InvocationTargetException, NoSuchMethodException, SecurityException {
			return classData.getDeclaredConstructor(parameterTypes).newInstance(initargs);
		}

		public boolean doesExtend(final Class<?> superClass) {
			return superClass.isAssignableFrom(classData);
		}

		@SuppressWarnings("unchecked")
		public <T> Class<? extends T> getClassObject() {
			if (!doesExtend(NonDeterministicChoice.class)) {
				throw new ClassCastException(
						"LoadedClass " + className + " does not implement " + NonDeterministicChoice.class.getName());
			}
			return (Class<? extends T>) classData;
		}

		public String encodeClassData() { // TODO
			System.out.println("Data of class \"" + className + "\"");
			System.out.println("Source file: " + sourceFile);
			System.out.println("Compiled file: " + compiledFile.getAbsolutePath());
			for (final File importClass : imports) {
				System.out.println("Import: " + importClass);
			}
			return "";
		}

		public static LoadedClass restoreClassData(final String data) { // TODO
			return null;
		}
	}

	public static void test() throws IOException, ClassNotFoundException {
		final String sb = "package " + getOutPackage() + ";\n" + "import java.util.ArrayList;\n"
				+ "import dummdumm.Dummy;"
				+ "import de.uni_freiburg.informatik.ultimate.plugins.cfgexecuter.compiler.*;\n"
				+ "import de.uni_freiburg.informatik.ultimate.plugins.cfgexecuter.evaluation.*;\n"
				+ "public class Test implements NonDeterministicChoice {\n" + "	private int seed;\n"
				+ "	public Test(int mSeed) {\n" + "		seed = mSeed;\n" + "		new Dummy(seed + \"\");\n" + "	}\n"
				+ "	@Override\n" + "	public <T> T chooseEdge(ArrayList<T> edges) {\n"
				+ "		int index = Math.abs(havocInt()) % edges.size();\n" + "		return edges.get(index);\n" + "	}\n"
				+ "	@Override\n" + "	public int havocInt() {\n" + "		return xorShift();\n" + "	}\n"
				+ "	@Override\n" + "	public boolean havocBool() {\n"
				+ "		return xorShift() < 0; // == is first bit 0 or 1\n" + "	}\n" + "	@Override\n"
				+ "	public BitVector havocBitVector() {\n" + "		return null;\n" + "	}\n" + "	@Override\n"
				+ "	public boolean areArraysEqual(Object a, Object b) {\n" + "		return havocBool();\n" + "	}\n"
				+ "	private int xorShift() {\n" + "		seed ^= seed << 13;\n" + "		seed ^= seed >> 17;\n"
				+ "		seed ^= seed << 5;\n" + "		return seed;\n" + "	}" + "}";

		final ArrayList<File> classes = new ArrayList<>();
		final File dummySource = new File("C:/Users/Frederic/Desktop/Dummy.java");
		final String dummyName = connectPath("dummdumm", "Dummy");
		final File dummy = createFile(dummySource, dummyName);
		compileClass(dummy, dummyName, classes);

		final String testName = connectPath(packagePath, outputFolder, "Test");
		final File main = createFile(sb, testName);
		classes.add(dummy);
		classes.add(openPluginClassFile("evaluation/BitVector"));
		classes.add(openPluginClassFile("compiler/NonDeterministicChoice"));
		final LoadedClass result = loadClass(main, testName, classes);
		try {
			result.encodeClassData();

			final Random random = new Random();
			final int seed = random.nextInt();
			final NonDeterministicChoice e = result.createInstance(NonDeterministicChoice.class,
					new Class<?>[] { int.class }, new Object[] { seed });

			/*
			 * System.out.println("Havoc Tests (Seed: "+seed+"):"); System.out.println("Int:    " + e.havocInt(null));
			 * System.out.println("Int:    " + e.havocInt(intVar)); System.out.println("Bool:   " + e.havocBool());
			 * System.out.println("Bool:   " + e.havocBool());
			 */
			final ArrayList<String> edges = new ArrayList<>();
			edges.add("a");
			edges.add("b");
			edges.add("c");
			edges.add("d");
			System.out.println("Choice: " + e.chooseEdge(edges));
			System.out.println("Choice: " + e.chooseEdge(edges));
			System.out.println("Choice: " + e.chooseEdge(edges));
			System.out.println("(Options for choice: [" + String.join(", ", edges) + "])");
		} catch (final InstantiationException e) {
			e.printStackTrace();
		} catch (final IllegalAccessException e) {
			e.printStackTrace();
		} catch (final IllegalArgumentException e) {
			e.printStackTrace();
		} catch (final InvocationTargetException e) {
			e.printStackTrace();
		} catch (final NoSuchMethodException e) {
			e.printStackTrace();
		} catch (final SecurityException e) {
			e.printStackTrace();
		}
	}

}
