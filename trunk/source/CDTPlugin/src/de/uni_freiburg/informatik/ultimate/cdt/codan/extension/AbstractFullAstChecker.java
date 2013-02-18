/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan.extension;

import org.eclipse.cdt.codan.core.cxx.model.AbstractIndexAstChecker;
import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.model.CModelException;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.ICElement;
import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.OperationCanceledException;

/**
 * So we need this Extension, because Codan uses internally the
 * 
 * PARSE_OPTION =
 * ITranslationUnit.AST_SKIP_TRIVIAL_EXPRESSIONS_IN_AGGREGATE_INITIALIZERS
 * 
 * So we have no trivial values in Arrays Initializer, this class solves this
 * problem. In order to do this we did not use any longer the internal Codan
 * Model Cache.
 * 
 * @author Stefan Wissert
 * 
 */
public abstract class AbstractFullAstChecker extends AbstractIndexAstChecker {

	/**
	 * Parsing Options for creating the used AST
	 */
	private static final int PARSE_MODE = ITranslationUnit.AST_SKIP_ALL_HEADERS
			| ITranslationUnit.AST_CONFIGURE_USING_SOURCE_CONTEXT
			| ITranslationUnit.AST_PARSE_INACTIVE_CODE;

	private IFile file;

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.cdt.codan.core.cxx.model.AbstractIndexAstChecker#getFile()
	 */
	@Override
	protected IFile getFile() {
		return file;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.cdt.codan.core.cxx.model.AbstractIndexAstChecker#processResource
	 * (org.eclipse.core.resources.IResource)
	 */
	@Override
	public synchronized boolean processResource(IResource resource)
			throws OperationCanceledException {
		if (!shouldProduceProblems(resource))
			return false;
		if (!(resource instanceof IFile))
			return true;

		processFile((IFile) resource);
		return false;
	}

	/**
	 * This methods generate a AST out of a File
	 * 
	 * @param file
	 * @throws OperationCanceledException
	 */
	private void processFile(IFile file) throws OperationCanceledException {
		this.file = file;
		ICElement celement = CoreModel.getDefault().create(file);
		if (!(celement instanceof ITranslationUnit)) {
			return;
		}
		ITranslationUnit tu = (ITranslationUnit) celement;
		ICProject[] projects;
		try {
			projects = CoreModel.getDefault().getCModel().getCProjects();
			IIndex index = CCorePlugin.getIndexManager().getIndex(projects);
			index.acquireReadLock();
			IASTTranslationUnit ast = tu.getAST(index, PARSE_MODE);
			if (ast != null) {
				synchronized (ast) {
					processAst(ast);
				}
			}
		} catch (CModelException e1) {
			e1.printStackTrace();
		} catch (CoreException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}
}
