/*
 * Project:	de.uni_freiburg.informatik.ultimate.dev.eclipse.templates
 * Package:	de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.wizards
 * File:	UltimatePluginSupport.java created on Feb ,  by Bj�rn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.wizards;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData.PluginType;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.ActivatorGenerator;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.BuildPropertiesGenerator;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.ClasspathGenerator;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.DotProjectGenerator;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.ManifestGenerator;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.ObserverGenerator;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.ParserPluginGenerator;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.PluginClassGenerator;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.filegenerators.PluginXmlGenerator;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

/**
 * UltimatePluginSupport
 * 
 * @author Bj�rn Buchhold
 * 
 */
public class UltimatePluginSupport {

	private static final String PLUGIN_PROJECT_NATURE = "org.eclipse.pde.PluginNature";
	private static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	public static final String PACKAGE_PREFIX_PATH = "src/de/uni_freiburg/informatik/ultimate/plugins/";

	/**
	 * @param projectName
	 * @param location
	 * @param monitor 
	 * @param natureId
	 * @return
	 */
	public static IProject createProject(String projectName, URI location, UltimatePluginData data, IProgressMonitor monitor) {
		Assert.isNotNull(projectName);
		Assert.isTrue(projectName.trim().length() > 0);

		IProject project = createBaseProject(projectName, location, monitor);
		try {
			addNature(project);

			String packagePath = PACKAGE_PREFIX_PATH + data.getTypeString() + "/" + data.getPluginName().toLowerCase();
			String metaInfPath =  "META-INF"; 
			String[] paths = {packagePath, metaInfPath}; //$NON-NLS-$ //$NON-NLS-$
			addToProjectStructure(project, paths, monitor);
			createFiles(project, packagePath, metaInfPath, data, monitor);
		} catch (CoreException e) {
			e.printStackTrace();
			project = null;
		}

		return project;
	}

	/**
	 * void createFiles
	 * @param project 
	 * @param packagePath
	 * @param metaInfPath
	 * @param data 
	 * @param monitor 
	 * @throws CoreException 
	 */
	private static void createFiles(IProject project, String packagePath, String metaInfPath, UltimatePluginData data, IProgressMonitor monitor) throws CoreException {
		//create files in project root
		IFile dotProject = project.getFile(".project");
		createFile(dotProject, new DotProjectGenerator().generate(data), monitor);
		IFile classpath = project.getFile(".classpath");
		createFile(classpath, new ClasspathGenerator().generate(data), monitor);
		IFile pluginXml = project.getFile("plugin.xml");
		createFile(pluginXml, new PluginXmlGenerator().generate(data), monitor);
		IFile buildProperties = project.getFile("build.properties");
		createFile(buildProperties, new BuildPropertiesGenerator().generate(data), monitor);
		
		//create files in META-INF
		IFolder metaInf = project.getFolder(metaInfPath);
		IFile manifest = metaInf.getFile("MANIFEST.MF");
		createFile(manifest, new ManifestGenerator().generate(data), monitor);
		
		//create source files
		IFolder src = project.getFolder(packagePath);
		IFile activator = src.getFile("Activator.java");
		createFile(activator, new ActivatorGenerator().generate(data), monitor);
		if(!(data.getType() == PluginType.source)){
			IFile mainclass = src.getFile(data.getPluginName()+".java");
			createFile(mainclass, new PluginClassGenerator().generate(data), monitor);
			IFile observer = src.getFile(data.getPluginName()+"Observer.java");
			createFile(observer, new ObserverGenerator().generate(data), monitor);
		}else{
			IFile mainclass = src.getFile(data.getPluginName()+".java");
			createFile(mainclass, new ParserPluginGenerator().generate(data), monitor);
		}
		
	}

	/**
	 * void createFile
	 * @param monitor 
	 * @param manifest
	 * @param string
	 * @throws CoreException 
	 */
	private static void createFile(IFile file, String content, IProgressMonitor monitor) throws CoreException {
		InputStream source =  new ByteArrayInputStream(content.getBytes());
		try{
			if (file.exists()) {
				file.setContents(source, true, true, monitor);
			} else {
				file.create(source, true, monitor);
			}
			source.close();
		}catch (IOException e){}
	}

	/**
	 * Just do the basics: create a basic project.
	 * 
	 * @param location
	 * @param projectName
	 * @param monitor 
	 */
	private static IProject createBaseProject(String projectName, URI location, IProgressMonitor monitor) {
		// it is acceptable to use the ResourcesPlugin class
		IProject newProject = ResourcesPlugin.getWorkspace().getRoot()
				.getProject(projectName);

		if (!newProject.exists()) {
			URI projectLocation = location;
			IProjectDescription desc = newProject.getWorkspace()
					.newProjectDescription(newProject.getName());
			if (location != null
					&& ResourcesPlugin.getWorkspace().getRoot()
							.getLocationURI().equals(location)) {
				projectLocation = null;
			}

			desc.setLocationURI(projectLocation);
			try {
				newProject.create(desc, monitor);
				if (!newProject.isOpen()) {
					newProject.open(monitor);
				}
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}

		return newProject;
	}

	private static void createFolder(IFolder folder, IProgressMonitor monitor) throws CoreException {
		IContainer parent = folder.getParent();
		if (parent instanceof IFolder) {
			createFolder((IFolder) parent, monitor);
		}
		if (!folder.exists()) {
			folder.create(false, true, monitor);
		}
	}

	/**
	 * Create a folder structure with a parent root, overlay, and a few child
	 * folders.
	 * 
	 * @param newProject
	 * @param paths
	 * @param monitor 
	 * @throws CoreException
	 */
	private static void addToProjectStructure(IProject newProject,
			String[] paths, IProgressMonitor monitor) throws CoreException {
		for (String path : paths) {
			IFolder etcFolders = newProject.getFolder(path);
			createFolder(etcFolders, monitor);
		}
	}

	private static void addNature(IProject project) throws CoreException {
		if (!project.hasNature(JAVA_NATURE)) {
			IProjectDescription description = project.getDescription();
			String[] prevNatures = description.getNatureIds();
			String[] newNatures = new String[prevNatures.length + 1];
			System.arraycopy(prevNatures, 0, newNatures, 0, prevNatures.length);
			newNatures[prevNatures.length] = JAVA_NATURE;
			description.setNatureIds(newNatures);

			IProgressMonitor monitor = null;
			project.setDescription(description, monitor);
		}
		if (!project.hasNature(PLUGIN_PROJECT_NATURE)) {
			IProjectDescription description = project.getDescription();
			String[] prevNatures = description.getNatureIds();
			String[] newNatures = new String[prevNatures.length + 1];
			System.arraycopy(prevNatures, 0, newNatures, 0, prevNatures.length);
			newNatures[prevNatures.length] = PLUGIN_PROJECT_NATURE;
			description.setNatureIds(newNatures);

			IProgressMonitor monitor = null;
			project.setDescription(description, monitor);
		}

	}
}
