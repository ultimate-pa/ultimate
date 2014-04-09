package de.uni_freiburg.informatik.ultimate.cdt.codan;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.cdt.Activator;
import de.uni_freiburg.informatik.ultimate.core.controllers.BaseExternalExecutionController;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ExternalParserToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.gui.preferencepages.UltimatePreferencePageFactory;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

/**
 * @author dietsch
 */
public class CDTController extends BaseExternalExecutionController {

	private Toolchain mToolchain;
	private IElement mAST;

	public CDTController() {
		super();
	}

	@Override
	public int init(ICore core) {
		// we create preference pages right after Ultimate has been initialized
		// and before it delegates control to the controller
		new UltimatePreferencePageFactory(mActualCore).createPreferencePages();
		return super.init(core);
	}

	@Override
	protected void createAndRunToolchainJob() throws Throwable {
		BasicToolchainJob tcj = new ExternalParserToolchainJob("Processing Toolchain", mCurrentCoreReference, this,
				BasicToolchainJob.ChainMode.RUN_TOOLCHAIN, mAST, new GraphType(getPluginID(), GraphType.Type.AST,
						new ArrayList<String>()));
		tcj.schedule();
		tcj.join();
	}

	public void runToolchain(String toolchain, IASTTranslationUnit ast) {
		try {
			mToolchain = new Toolchain(toolchain);
			mAST = new WrapperNode(null, ast);
			nextRun();

		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (JAXBException e) {
			e.printStackTrace();
		} catch (SAXException e) {
			e.printStackTrace();
		}
	}

	@Override
	public String getName() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public ISource selectParser(Collection<ISource> parser) {
		throw new UnsupportedOperationException("This Method should never be called for this controller!");
	}

	@Override
	public Toolchain selectTools(List<ITool> tools) {
		return mToolchain;
	}

	@Override
	public List<String> selectModel(List<String> modelNames) {
		ArrayList<String> returnList = new ArrayList<String>();
		for (String model : modelNames) {
			if (model.contains("CACSL2BoogieTranslator")) {
				returnList.add(model);
			}
		}
		if (returnList.isEmpty()) {
			returnList.addAll(modelNames);
		}
		return returnList;
	}

	@Override
	public void displayToolchainResultProgramIncorrect() {
	}

	@Override
	public void displayToolchainResultProgramCorrect() {
	}

	@Override
	public void displayToolchainResultProgramUnknown(String description) {
	}

	@Override
	public void displayException(String description, Throwable ex) {

	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

}
