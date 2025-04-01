package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

import org.osgi.framework.Bundle;
import org.osgi.framework.wiring.BundleWiring;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.JavaCodeEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.SimpleState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Update;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class DynamicLoader {
	/** Base package of this project, same as first line of file */
	private final static String mPackageName;
	/** Base folder of this project, is {@link #mPackageName} with periods replaced by {@link File#separator} */
	private final static String mPackagePath;
	/** File pointing to the directory containing this project, like /ultimate/trunk/source/IcfgInterpreter */
	private final static File mProjectDirectory;
	/** Absolute path of the file {@link #mProjectDirectory} (for convenience) */
	private final static String mProjectPath;
	/** Folder pointing to the destination of compiled classes */
	private final static String mOutputPath;
	/** Package name of compiled classes */
	private final static String mOutputPackage;

	static {
		File projectDir;
		try {
			projectDir = getProjectOfClass(DynamicLoader.class);
		} catch (final URISyntaxException e) {
			e.printStackTrace();
			projectDir = null;
		}
		mProjectDirectory = projectDir;

		mPackageName = IcfgInterpreter.class.getPackageName();
		mPackagePath = connectPath(mPackageName.split("[.]"));
		mProjectPath = mProjectDirectory.getAbsolutePath();
		mOutputPath = connectPath(mPackagePath, "compiled", "ICFG_Out");
		mOutputPackage = mOutputPath.replace(File.separator, ".");
	}

	private static String connectPath(final String... parts) {
		return String.join(File.separator, parts);
	}

	/**
	 * @return The file pointing to the base directory of this plug-in: <br>
	 *         Like .../ultimate/trunk/source/IcfgInterpreter/
	 */
	public static File getProjectSourceDirectory() {
		return mProjectDirectory;
	}

	private static class WrongFileExtensionException extends IOException {
		private static final long serialVersionUID = 654321L;

		public WrongFileExtensionException(final String message) {
			super(message);
		}
	}

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
		return createFile(mCode, codeFile);
	}

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
	public static File createFile(final String mCode, final File codeFile) throws IOException {
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
		final File originalFile = new File(connectPath(mProjectPath, "src", mPackagePath, className + ".java"));
		final File tempFile = new File(connectPath(mPackagePath, className + ".java"));
		tempFile.getParentFile().mkdirs();
		Files.copy(originalFile.toPath(), tempFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
		return tempFile;
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
	public static File openOutsideClassFile(final String className, final String projectName, final String packagePath)
			throws IOException {
		final File originalFile = new File(connectPath(mProjectDirectory.getParentFile().getAbsolutePath(), projectName,
				"src", packagePath, className + ".java"));
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
	public static File openOutsideClassFile(final File sourceFile, final String packagePath, final String className)
			throws IOException {
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
		final File loadableFile = new File(connectPath(mProjectPath, "bin", className + ".class"));
		loadableFile.getParentFile().mkdirs();
		Files.copy(compiledFile.toPath(), loadableFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
		return loadableFile;
	}

	public static File compileClass(final File mainFile, final String className, final HashSet<File> javaFiles,
			final ArrayList<File> projectDirectories) throws ClassCastException, IOException {
		javaFiles.add(mainFile);

		final DiagnosticCollector<JavaFileObject> diagnosticListener = new DiagnosticCollector<>();
		final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
		final StandardJavaFileManager fileManager = compiler.getStandardFileManager(diagnosticListener, null, null);

		final Iterable<? extends JavaFileObject> compilationUnits = fileManager.getJavaFileObjectsFromFiles(javaFiles);

		final ArrayList<String> classPaths = new ArrayList<>();

		for (final File dir : projectDirectories) {
			// check if file is a valid directory
			if (dir == null || !dir.exists() || !dir.isDirectory()) {
				continue;
			}
			// check if file has required bin folder
			final File projectDir = new File(dir, "bin");
			if (!projectDir.exists() || !projectDir.isDirectory()) {
				continue;
			}
			classPaths.add(projectDir.getAbsolutePath());
		}

		final ArrayList<String> options = new ArrayList<>();
		if (classPaths.size() > 0) {
			options.add("-classpath");
			options.add(String.join(File.pathSeparator, classPaths));
		}

		final JavaCompiler.CompilationTask task = compiler.getTask(null, fileManager, diagnosticListener, options, null,
				compilationUnits);

		final boolean success = task.call();
		fileManager.close();

		javaFiles.remove(mainFile);

		if (!success) {
			final StringBuilder error = new StringBuilder("Encountered failure while compiling.\n");
			for (final Diagnostic<? extends JavaFileObject> diagnostic : diagnosticListener.getDiagnostics()) {
				error.append("\nError on line ").append(diagnostic.getLineNumber());
				final JavaFileObject sourceFile = diagnostic.getSource();
				if (sourceFile != null) {
					error.append(" of java file ").append(sourceFile.getName());
				}
				error.append("\n");
				error.append(diagnostic.getMessage(null));
			}
			IcfgInterpreterObserver.getLogger().error(error);
			return null;
		}

		final File compiledFile = new File(mainFile.getParentFile(), mainFile.getName().replace(".java", ".class"));
		return copyToBin(compiledFile, className);
	}

	/**
	 * TODO Compiles the given files and creates a {@link LoadedClass} object. <br>
	 * Usage: <br>
	 * {@code LoadedClass loadedClass = DynamicLoader.loadClass(main, imports, name);} <br>
	 * {@code InterfaceClass instance = loadedClass.createInstance(InterfaceClass.class, paramTypes, paramValues);}
	 *
	 * @param mainFile           .java file that contains the class to be loaded. This class should extend some
	 *                           interface such that <br>
	 *                           (Obtained via {@link #createFile(File)} or {@link #createFile(String, String)}
	 * @param className          Name of the target class in <strong>mainFile</strong>.
	 * @param importFiles        List of .java files that are imported by either <strong>classFile</strong> or any file
	 *                           of <strong>importFiles</strong>. <br>
	 *                           (Obtained via {@link #openPluginClassFile(String)} or
	 *                           {@link #openOutsideClassFile(File)})
	 * @param projectDirectories
	 * @return A {@link LoadedClass} that can create instances of the target class as objects of the interface.
	 */
	public static LoadedClass loadClass(final File mainFile, final String className, final HashSet<File> importFiles,
			final ArrayList<File> projectDirectories) throws ClassNotFoundException, ClassCastException, IOException {
		final File compiledFile = compileClass(mainFile, className, importFiles, projectDirectories);

		final Activator act = Activator.getInstance();
		final Bundle bundle = act.getBundle();
		final BundleWiring bundleW = bundle.adapt(BundleWiring.class);
		final ClassLoader cl = bundleW.getClassLoader();

		final Class<?> loadedClass = cl.loadClass(className.replace(File.separator, "."));

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
		private final HashSet<File> imports;
		private final Class<?> classData;

		private LoadedClass(final String mClassName, final File mSourceFile, final File mCompiledFile,
				final HashSet<File> mImports, final Class<?> mClassData) {
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

	/**
	 * Get a file object pointing to the root directory of the Ultimate project that the given class is defined in.
	 *
	 * @param clazz The class of the project
	 * @return A file pointing to a folder like <strong>{@literal <}ultimate root
	 *         folder{@literal >}/trunk/source/{@literal <}project folder{@literal >}</strong>
	 * @throws URISyntaxException
	 */
	public static File getProjectOfClass(final Class<?> clazz) throws URISyntaxException {
		return new File(clazz.getProtectionDomain().getCodeSource().getLocation().toURI().normalize().getPath());
	}

	private static String makeImport(final Class<?> clazz) {
		return "import " + clazz.getName() + ";\n";
	}

	public static JavaCodeEdge makeCodeEdge(final ICFGExecutionEdge edge, final File compileDirectory)
			throws IOException {
		final String className = "JCEdge_" + edge.getUniqueName().replace("-", "_").replace("#", "_");

		final ArrayList<Class<?>> parameterClasses = new ArrayList<>();
		final ArrayList<Object> parameterObjects = new ArrayList<>();
		parameterClasses.add(IcfgLocation.class);
		parameterClasses.add(IcfgLocation.class);
		parameterObjects.add(edge.mSource);
		parameterObjects.add(edge.mTarget);
		final StringBuilder parameters = new StringBuilder("IcfgLocation int_source, IcfgLocation int_target");
		String programVarFields = null;
		String programVarAssignments = "";

		final HashSet<IProgramVar> programVars = new HashSet<>();
		for (final Variable variable : edge.getVariables()) {
			final IProgramVar programVar = variable.getVariableTerm().programVar;
			if (programVar == null) {
				continue;
			}
			if (!programVars.add(programVar)) {
				continue;
			}
			parameterClasses.add(IProgramVar.class);
			if (programVarFields == null) {
				programVarFields = "private final IProgramVar m" + programVar.getGloballyUniqueId();
			} else {
				programVarFields += ", m" + programVar.getGloballyUniqueId();
			}
			parameters.append(", IProgramVar ext_").append(programVar.getGloballyUniqueId());
			programVarAssignments += "\n\t\tthis.m" + programVar.getGloballyUniqueId() + " = ext_"
					+ programVar.getGloballyUniqueId() + ";";
			parameterObjects.add(programVar);
		}
		if (programVarFields != null) {
			programVarFields += ";\n\t";
		} else {
			programVarFields = "";
			programVarAssignments = "";
		}

		final Class<?>[] paramClasses = Util.fillArray(parameterClasses, new Class<?>[parameterClasses.size()]);
		final Object[] paramObjects = Util.fillArray(parameterObjects, new Object[parameterObjects.size()]);

		final Update[] updates = edge.getUpdates();
		final StringBuilder updateCode = new StringBuilder();
		for (final Update update : updates) {
			updateCode.append("\t\t").append(update.toCode()).append("\n");
		}

		final StringBuilder codeB = new StringBuilder();
		codeB.append("package " + mOutputPackage + ";\n\n");
		codeB.append(makeImport(IProgramVar.class));
		codeB.append(makeImport(IcfgLocation.class));
		codeB.append(makeImport(SimpleState.class));
		codeB.append(makeImport(JavaCodeEdge.class));
		codeB.append(makeImport(Math.class));
		codeB.append(makeImport(BitVector.class));
		codeB.append(makeImport(NonDeterministicChoice.class));
		codeB.append(makeImport(SMTArray.class));
		codeB.append(makeImport(Util.class));
		codeB.append("\npublic class " + className + " implements " + JavaCodeEdge.class.getSimpleName() + " {\n");
		codeB.append("\tpublic final IcfgLocation source, target;\n\t");
		codeB.append(programVarFields);
		codeB.append("\n\tpublic " + className + "(").append(parameters).append(") {\n");
		codeB.append("\t\tthis.source = int_source;\n\t\tthis.target = int_target;");
		codeB.append(programVarAssignments).append("\n\t}\n");
		codeB.append("\tpublic IcfgLocation getSource() {\n\t\treturn source;\n\t}\n\n");
		codeB.append("\tpublic IcfgLocation getTarget() {\n\t\treturn target;\n\t}\n\n");
		codeB.append("\tpublic boolean guard(final SimpleState currentState) {\n");
		codeB.append("\t\treturn " + edge.getGuard().toCode().replace("nextState", "currentState") + ";\n\t}\n\n");
		codeB.append("\tpublic SimpleState update(final SimpleState currentState) {\n");
		codeB.append("\t\tfinal SimpleState nextState = currentState.clone();\n");
		codeB.append(updateCode.toString());
		codeB.append("\t\treturn nextState;\n").append("\t}\n").append("}").toString();

		final String code = codeB.toString();
		final String classFullName = connectPath(mOutputPath, className);
		final File codeFile = new File(compileDirectory, classFullName + ".java");
		final File main = createFile(code, codeFile);

		try {
			final ArrayList<File> neededProjects = new ArrayList<>();
			neededProjects.add(getProjectOfClass(IcfgInterpreter.class));
			neededProjects.add(getProjectOfClass(IProgramVar.class));
			final LoadedClass stateClass = loadClass(main, classFullName, new HashSet<>(), neededProjects);
			final JavaCodeEdge stateCreator = stateClass.createInstance(JavaCodeEdge.class, paramClasses, paramObjects);
			return stateCreator;
		} catch (final Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	public static HashMap<IcfgLocation, JavaCodeEdge[]> makeUpdates(
			final HashMap<IcfgLocation, ArrayList<ICFGExecutionEdge>> edges) {
		try {
			final File compileDir = Files.createTempDirectory("IcfgInterpreterCompile").toFile();
			final HashMap<IcfgLocation, JavaCodeEdge[]> out = new HashMap<>();
			for (final IcfgLocation location : edges.keySet()) {
				final ArrayList<ICFGExecutionEdge> outEdges = edges.get(location);
				final JavaCodeEdge[] compiledEdges = new JavaCodeEdge[outEdges.size()];
				for (int i = 0; i < compiledEdges.length; i++) {
					compiledEdges[i] = makeCodeEdge(outEdges.get(i), compileDir);
				}
				out.put(location, compiledEdges);
			}
			return out;
		} catch (final Exception e) {
			e.printStackTrace();
		}
		return null;
	}
}