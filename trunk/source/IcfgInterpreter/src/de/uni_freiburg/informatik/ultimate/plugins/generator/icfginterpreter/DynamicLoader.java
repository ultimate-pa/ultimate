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

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.EnumState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.IVariableName;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.JavaCodeEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.InterpretedIcfg;
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
		final File codeFile = new File(className + ".java");
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
	 * {@link DynamicLoader#loadClass(File, String, HashSet, ArrayList)}. <br>
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

		public String encodeClassData() { // TODO
			System.out.println("Data of class \"" + className + "\"");
			System.out.println("Source file: " + sourceFile);
			System.out.println("Compiled file: " + compiledFile.getAbsolutePath());
			for (final File importClass : imports) {
				System.out.println("Import: " + importClass);
			}
			return "";
		}

		@SuppressWarnings("unchecked")
		public <T> Class<T> getClassObject(final Class<T> interfaceClass) {
			if (!interfaceClass.isAssignableFrom(classData)) {
				throw new ClassCastException(
						"Compiled class " + className + " does not implement " + interfaceClass.getName());
			}
			return (Class<T>) classData;
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

	public static String getVersionedClassName(final String baseName) {
		return baseName + "_v" + IcfgInterpreterObserver.getInstance().getCurrentICFGCardinality();
	}

	public static final String enumClassBaseName = "VariableName";

	@SuppressWarnings("unchecked")
	public static <T extends Enum<T> & IVariableName> Class<T> makeVariableNameEnum(final HashSet<Variable> variables)
			throws IOException, URISyntaxException, ClassNotFoundException, ClassCastException {
		final String versionedEnumClassName = getVersionedClassName(enumClassBaseName);
		final StringBuilder code = new StringBuilder();
		code.append("package " + mOutputPackage + ";\n\n");
		code.append(makeImport(HashSet.class));
		code.append(makeImport(IProgramVar.class));
		code.append(makeImport(IVariableName.class));
		code.append("\npublic enum ").append(versionedEnumClassName).append(" implements ")
				.append(IVariableName.class.getSimpleName()).append(" {\n\t");

		final HashSet<IProgramVar> visited = new HashSet<>();
		for (final Variable variable : variables) {
			final IProgramVar programVar = variable.getVariableTerm().mProgramVar;
			if (programVar == null || visited.contains(programVar)) {
				continue;
			}
			visited.add(programVar);
			code.append(programVar.getGloballyUniqueId()).append(", ");
		}
		code.append(";\n\n");
		code.append("\tprivate IProgramVar mProgramVar;\n\n");
		code.append("\t@Override\n");
		code.append("\tpublic void initiate(final HashSet<IProgramVar> progVars) {\n");
		code.append("\t\tfor (final IProgramVar progVar : progVars) {\n");
		code.append("\t\t\tvalueOf(progVar.getGloballyUniqueId()).mProgramVar = progVar;\n");
		code.append("\t\t}\n");
		code.append("\t}\n\n");
		code.append("\t@Override\n");
		code.append("\tpublic IProgramVar getProgramVar() {\n");
		code.append("\t\treturn mProgramVar;\n");
		code.append("\t}\n}");

		final String classFullName = connectPath(mOutputPath, versionedEnumClassName);

		final File codeFile = new File(compileDir, classFullName + ".java");

		final HashSet<IProgramVar> progVars = Util.map(variables, (variable) -> {
			return variable.getVariableTerm().mProgramVar;
		}, new HashSet<>());
		progVars.remove(null);

		final File main = createFile(code.toString(), codeFile);
		final ArrayList<File> neededProjects = new ArrayList<>();
		neededProjects.add(getProjectOfClass(IVariableName.class));
		neededProjects.add(getProjectOfClass(IProgramVar.class));
		final LoadedClass enumClass = loadClass(main, classFullName, new HashSet<>(), neededProjects);

		final Enum<?>[] enumConstants = enumClass.classData.asSubclass(Enum.class).getEnumConstants();
		if (enumConstants.length > 0) {
			final IVariableName a = (IVariableName) enumConstants[0];
			a.initiate(progVars);
		}

		return (Class<T>) enumClass.classData.asSubclass(Enum.class);

	}

	public static String getVarLookup(final IProgramVar programVar) {
		return getVersionedClassName(enumClassBaseName) + "." + programVar.getGloballyUniqueId();
	}

	private static String makeImport(final Class<?> clazz) {
		return "import " + clazz.getName() + ";\n";
	}

	@SuppressWarnings("unchecked")
	public static <T extends Enum<T> & IVariableName> JavaCodeEdge<T> makeCodeEdge(final ICFGExecutionEdge edge,
			final Class<T> enumClass) {
		final String enumClassName = enumClass.getSimpleName();
		final String uniqueNameSafe = edge.getUniqueName().replace("-", "_").replace("#", "_");
		final String className = getVersionedClassName("JCEdge_" + uniqueNameSafe);

		final String stateType = EnumState.class.getSimpleName() + "<" + enumClassName + ">";

		final StringBuilder code = new StringBuilder();
		code.append("package " + mOutputPackage + ";\n\n");
		code.append(makeImport(Math.class));
		code.append(makeImport(IProgramVar.class));
		code.append(makeImport(IcfgLocation.class));
		// code.append(makeImport(ModifiableExplicitEdgesMultigraph.class));
		// code.append(makeImport(IElement.class));
		code.append(makeImport(BitVector.class));
		code.append(makeImport(NonDeterministicChoice.class));
		code.append(makeImport(SMTArray.class));
		code.append(makeImport(Util.class));
		code.append(makeImport(EnumState.class));
		code.append(makeImport(JavaCodeEdge.class));
		code.append(makeImport(IntegerRestriction.class));
		code.append(makeImport(BooleanRestriction.class));
		code.append(makeImport(ArrayRestriction.class));
		code.append(makeImport(BitVectorRestriction.class));
		code.append(makeImport(UnmodifiableTransFormula.class));
		code.append("import ").append(mOutputPackage).append(".").append(enumClassName).append(";\n\n");
		code.append("public class " + className + " implements " + JavaCodeEdge.class.getSimpleName() + "<"
				+ enumClassName + "> {\n");
		code.append("\tpublic final IcfgLocation source, target;\n");
		code.append("\tpublic final UnmodifiableTransFormula mFormula;\n\n");
		code.append("\tpublic " + className
				+ "(IcfgLocation int_source, IcfgLocation int_target, UnmodifiableTransFormula int_formula) {\n");
		code.append("\t\tsource = int_source;\n\t\ttarget = int_target;\n");
		code.append("\t\tmFormula = int_formula;\n");
		code.append("\t}\n");
		code.append("\t@Override\n");
		code.append("\tpublic IcfgLocation getSource() {\n\t\treturn source;\n\t}\n\n");
		code.append("\t@Override\n");
		code.append("\tpublic IcfgLocation getTarget() {\n\t\treturn target;\n\t}\n\n");

		code.append("\t@Override\n");
		code.append("\tpublic boolean guard(final " + stateType + " currentState) {\n");
		code.append("\t\treturn " + edge.getGuard().toCode().replace("nextState", "currentState") + ";\n\t}\n\n");
		code.append("\t@Override\n");
		code.append("\tpublic " + stateType + " update(final " + stateType + " currentState) {\n");
		code.append("\t\tfinal " + stateType + " nextState = currentState.clone();\n");

		final Update[] updates = edge.getUpdates();
		for (final Update update : updates) {
			code.append("\t\t").append(update.toCode()).append("\n");
		}
		code.append("\t\treturn nextState;\n");
		code.append("\t}\n\n");

		code.append("\t@Override\n");
		code.append("\tpublic String toString() {\n");
		code.append("\t\t return \"Edge \" + source.toString() + \" to \" + target.toString()")
				.append(" + \" with \" + mFormula.getFormula().toStringDirect();");
		code.append("\t}\n");

		code.append("}").toString();

		final String classFullName = connectPath(mOutputPath, className);
		final File codeFile = new File(compileDir, classFullName + ".java");

		try {
			final File main = createFile(code.toString(), codeFile);
			final ArrayList<File> neededProjects = new ArrayList<>();
			neededProjects.add(getProjectOfClass(IcfgInterpreter.class));
			neededProjects.add(getProjectOfClass(IProgramVar.class));
			neededProjects.add(getProjectOfClass(Term.class));
			neededProjects.add(getProjectOfClass(ModifiableExplicitEdgesMultigraph.class));
			neededProjects.add(getProjectOfClass(IElement.class));

			final LoadedClass stateClass = loadClass(main, classFullName, new HashSet<>(), neededProjects);

			final Class<?>[] paramClasses = { IcfgLocation.class, IcfgLocation.class, UnmodifiableTransFormula.class };
			final Object[] paramObjects = { edge.mSource, edge.mTarget, edge.getTransFormula() };

			return (JavaCodeEdge<T>) stateClass.createInstanceUncast(paramClasses, paramObjects);
		} catch (final Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	private static File compileDir = null;

	public static void makeCompilationDirectory() {
		try {
			compileDir = Files.createTempDirectory("IcfgInterpreterCompile").toFile();
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

	public static void deleteCompilationDirectory() {
		if (compileDir == null) {
			return;
		}
		deleteRecursive(compileDir);
		compileDir = null;
	}

	private static void deleteRecursive(final File file) {
		if (file.isDirectory()) {
			for (final File subFile : file.listFiles()) {
				deleteRecursive(subFile);
			}
		}
		file.delete();
	}

	public static <T extends Enum<T> & IVariableName> HashMap<IcfgLocation, ArrayList<JavaCodeEdge<T>>> makeUpdates(
			final InterpretedIcfg execIcfg, final Class<T> enumClass) {
		try {

			final HashMap<IcfgLocation, ArrayList<JavaCodeEdge<T>>> out = new HashMap<>();
			for (final IcfgLocation location : execIcfg.getLocations()) {
				final HashSet<ICFGExecutionEdge> outEdges = execIcfg.getOutEdges(location);
				final ArrayList<JavaCodeEdge<T>> compiledEdges = new ArrayList<>();
				for (final ICFGExecutionEdge outEdge : outEdges) {
					compiledEdges.add(makeCodeEdge(outEdge, enumClass));
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