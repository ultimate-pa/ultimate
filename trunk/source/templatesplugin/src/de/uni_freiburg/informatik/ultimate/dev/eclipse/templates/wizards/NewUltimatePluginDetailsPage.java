/*
 * Project:	de.uni_freiburg.informatik.ultimate.dev.eclipse.templates
 * Package:	de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.wizards
 * File:	NewUltimatePluginDetailsPage.java created on Mar 4, 2010 by Bj�rn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.wizards;

import java.util.LinkedList;
import java.util.List;
import java.util.StringTokenizer;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData.PluginType;
import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData.QueryKeyword;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * NewUltimatePluginDetailPage
 * 
 * @author Bj�rn Buchhold
 * 
 */
public class NewUltimatePluginDetailsPage extends WizardPage {

	// text fields
	private Text pluginNameText;
	private Text pluginIdText;
	private Text fileExtensionText;

	// plugin Type choice
	private Button typeAnalysisButton;
	private Button typeGeneratorButton;
	private Button typeOutputButton;
	private Button typeSourceButton;

	// obs choice
	private Button obsTrueButton;
	private Button obsFalseButton;

	// gui choice
	private Button guiReqTrueButton;
	private Button guiReqFalseButton;

	// query Keyword choice
	private Button qkwAllButton;
	private Button qkwAllAndPersistButton;
	private Button qkwSourceButton;
	private Button qkwToolButton;
	private Button qkwUserButton;
	private Button qkwLastButton;

	/**
	 * boolean managedObserver
	 */
	private Boolean managedObserver;

	/**
	 * Boolean guiRequired
	 */
	private Boolean guiRequired;

	/**
	 * PluginType pluginType
	 */
	private PluginType pluginType;

	/**
	 * QueryKeyword queryKeyword
	 */
	private QueryKeyword queryKeyword;

	/**
	 * @param pageName
	 */
	protected NewUltimatePluginDetailsPage(String pageName) {
		super(pageName);
		setPageComplete(false);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets
	 * .Composite)
	 */
	@Override
	public void createControl(Composite parent) {
		// declare listeners
		ModifyListener myModifyListener = new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		};

		// create the controls
		Composite container = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		container.setLayout(layout);
		layout.numColumns = 2;
		layout.verticalSpacing = 9;

		// enter the plug-in id
		Label label = new Label(container, SWT.NULL);
		label.setText("&Plug-in ID:");
		pluginIdText = new Text(container, SWT.BORDER | SWT.SINGLE);
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		pluginIdText.setLayoutData(gd);
		pluginIdText.addModifyListener(myModifyListener);

		// enter a name
		label = new Label(container, SWT.NULL);
		label.setText("&Plug-in name:");
		pluginNameText = new Text(container, SWT.BORDER | SWT.SINGLE);
		gd = new GridData(GridData.FILL_HORIZONTAL);
		pluginNameText.setLayoutData(gd);
		pluginNameText.addModifyListener(myModifyListener);

		// Choice of plugin type
		label = new Label(container, SWT.NULL);
		label.setText("&Plug-in type:");
		Composite ptContainer = new Composite(container, SWT.NULL);
		ptContainer.setLayout(new RowLayout());
		ptContainer.setEnabled(true);
		ptContainer.setVisible(true);
		typeAnalysisButton = new Button(ptContainer, SWT.RADIO);
		typeAnalysisButton.setEnabled(true);
		typeAnalysisButton.setText("Analysis");
		typeAnalysisButton
				.addSelectionListener(new PluginTypeSelectionListener(
						PluginType.analysis));
		typeGeneratorButton = new Button(ptContainer, SWT.RADIO);
		typeGeneratorButton.setEnabled(true);
		typeGeneratorButton.setText("Generator");
		typeGeneratorButton
				.addSelectionListener(new PluginTypeSelectionListener(
						PluginType.generator));
		typeOutputButton = new Button(ptContainer, SWT.RADIO);
		typeOutputButton.setEnabled(true);
		typeOutputButton.setText("Output");
		typeOutputButton.addSelectionListener(new PluginTypeSelectionListener(
				PluginType.output));

		typeSourceButton = new Button(ptContainer, SWT.RADIO);
		typeSourceButton.setEnabled(true);
		typeSourceButton.setText("Source");
		typeSourceButton.addSelectionListener(new PluginTypeSelectionListener(
				PluginType.source));

		// Choose observer kind
		label = new Label(container, SWT.NULL);
		label.setText("&Observer:");
		Composite obsContainer = new Composite(container, SWT.NULL);
		obsContainer.setLayout(new RowLayout());
		obsContainer.setEnabled(true);
		obsContainer.setVisible(true);
		obsTrueButton = new Button(obsContainer, SWT.RADIO);
		obsTrueButton.setData("managed", true);
		obsTrueButton.setEnabled(true);
		obsTrueButton.setText("managed");
		obsTrueButton.addSelectionListener(new ObserverSelectionListener(true));
		obsFalseButton = new Button(obsContainer, SWT.RADIO);
		obsFalseButton.setText("unmanaged");
		obsFalseButton.setData("unmanaged", false);
		obsFalseButton.setEnabled(true);
		obsFalseButton
				.addSelectionListener(new ObserverSelectionListener(false));

		// Choose query Keyword
		label = new Label(container, SWT.NULL);
		label.setText("&Query Keyword:");
		Composite qkwContainer = new Composite(container, SWT.NULL);
		qkwContainer.setLayout(new RowLayout());
		qkwContainer.setEnabled(true);
		qkwContainer.setVisible(true);
		qkwAllButton = new Button(qkwContainer, SWT.RADIO);
		qkwAllButton.setEnabled(true);
		qkwAllButton.setText("ALL");
		qkwAllButton.addSelectionListener(new QkwSelectionListener(
				QueryKeyword.ALL));
		qkwAllAndPersistButton = new Button(qkwContainer, SWT.RADIO);
		qkwAllAndPersistButton.setEnabled(true);
		qkwAllAndPersistButton.setText("ALLANDPERSIST");
		qkwAllAndPersistButton.addSelectionListener(new QkwSelectionListener(
				QueryKeyword.ALLANDPERSIST));
		qkwLastButton = new Button(qkwContainer, SWT.RADIO);
		qkwLastButton.setEnabled(true);
		qkwLastButton.setText("LAST");
		qkwLastButton.addSelectionListener(new QkwSelectionListener(
				QueryKeyword.LAST));
		qkwSourceButton = new Button(qkwContainer, SWT.RADIO);
		qkwSourceButton.setEnabled(true);
		qkwSourceButton.setText("SOURCE");
		qkwSourceButton.addSelectionListener(new QkwSelectionListener(
				QueryKeyword.SOURCE));
		qkwToolButton = new Button(qkwContainer, SWT.RADIO);
		qkwToolButton.setEnabled(true);
		qkwToolButton.setText("TOOL");
		qkwToolButton.addSelectionListener(new QkwSelectionListener(
				QueryKeyword.TOOL));
		qkwUserButton = new Button(qkwContainer, SWT.RADIO);
		qkwUserButton.setEnabled(true);
		qkwUserButton.setText("USER");
		qkwUserButton.addSelectionListener(new QkwSelectionListener(
				QueryKeyword.USER));

		// enter the parseble file extension
		label = new Label(container, SWT.NULL);
		label.setText("&Accepted file extensions \n(separated by whitespaces): ");
		fileExtensionText = new Text(container, SWT.BORDER | SWT.SINGLE);
		gd = new GridData(GridData.FILL_HORIZONTAL);
		fileExtensionText.setLayoutData(gd);
		fileExtensionText.addModifyListener(myModifyListener);
		fileExtensionText.setEnabled(false);

		// Choose if gui is required
		label = new Label(container, SWT.NULL);
		label.setText("&Requires GUI:");
		Composite rqContainer = new Composite(container, SWT.NULL);
		rqContainer.setLayout(new RowLayout());
		rqContainer.setEnabled(true);
		rqContainer.setVisible(true);
		guiReqTrueButton = new Button(rqContainer, SWT.RADIO);
		guiReqTrueButton.setData("GUI required", true);
		guiReqTrueButton.setEnabled(true);
		guiReqTrueButton.setText("GUI required");
		guiReqTrueButton.addSelectionListener(new GuiRequiredSelectionListener(
				true));
		guiReqFalseButton = new Button(rqContainer, SWT.RADIO);
		guiReqFalseButton.setText("works in commandline");
		guiReqFalseButton.setData("works in commandline", false);
		guiReqFalseButton.setEnabled(true);
		guiReqFalseButton
				.addSelectionListener(new GuiRequiredSelectionListener(false));

		dialogChanged();
		setControl(container);
	}

	/**
	 * Ensures that all fields are set correctly.
	 */
	private void dialogChanged() {
		String pluginId = getPluginId();
		if (pluginId.length() == 0) {
			updateStatus("Plug-in ID must be specified.");
			return;
		}
		if (pluginId.contains(" ")) {
			updateStatus("Plug-in ID may not contain whitespaces.");
			return;
		}
		String pluginName = getPluginName();
		if (pluginName.length() == 0) {
			updateStatus("Plug-in name must be specified.");
			return;
		}
		if (pluginName.contains(" ")) {
			updateStatus("Plug-in ID may not contain whitespaces or special characters.");
			return;
		}

		if (pluginType == null) {
			updateStatus("Select a plug-in type.");
			return;
		}
		if (pluginType != PluginType.source && managedObserver == null) {
			updateStatus("Select if you want to have a managed observer.");
			return;
		}
		if (pluginType != PluginType.source && queryKeyword == null) {
			updateStatus("Select a query Keyword.");
			return;
		}
		List<String> fileExtensions = getFileExtensions();
		if (pluginType == PluginType.source && fileExtensions.size() == 0) {
			updateStatus("Enter a file extension describing parsable files.");
			return;
		}
		if (guiRequired == null) {
			updateStatus("Select if the plug-in requires a gui controller to run.");
			return;
		}

		updateStatus(null);
	}

	public List<String> getFileExtensions() {
		StringTokenizer st = new StringTokenizer(fileExtensionText.getText());
		List<String> extensions = new LinkedList<String>();
		while(st.hasMoreTokens()){
			extensions.add(st.nextToken());
		}
		return extensions;
		
	}

	/**
	 * String getPluginId
	 * 
	 * @return
	 */
	public String getPluginId() {
		return pluginIdText.getText();
	}

	/**
	 * String getPluginName
	 * 
	 * @return <
	 */
	public String getPluginName() {
		return pluginNameText.getText();
	}

	/**
	 * PluginType getPluginType
	 * 
	 * @return
	 */
	public PluginType getPluginType() {
		return pluginType;
	}

	/**
	 * void updateStatus
	 * 
	 * @param message
	 */
	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

	/**
	 * boolean isManagedObserver
	 * 
	 * @return
	 */
	public boolean isManagedObserver() {
		return this.managedObserver;
	}

	public boolean isRequiresGui() {
		return this.guiRequired;
	}

	public UltimatePluginData getUltimatePluginData() {
		return new UltimatePluginData(getPluginId(), getPluginName(),
				getPluginType(), isManagedObserver(), isRequiresGui(),
				getFileExtensions(), getQueryKeyWord());
	}

	/**
	 * QueryKeyword getQueryKeyWord
	 * 
	 * @return
	 */
	private QueryKeyword getQueryKeyWord() {
		return this.queryKeyword;
	}

	private class ObserverSelectionListener implements SelectionListener {

		private boolean b;

		private ObserverSelectionListener(boolean b) {
			this.b = b;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org
		 * .eclipse.swt.events.SelectionEvent)
		 */
		@Override
		public void widgetDefaultSelected(SelectionEvent e) {
			dialogChanged();
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse
		 * .swt.events.SelectionEvent)
		 */
		@Override
		public void widgetSelected(SelectionEvent e) {
			managedObserver = b;
			dialogChanged();
		}

	}

	private class GuiRequiredSelectionListener implements SelectionListener {

		private boolean b;

		private GuiRequiredSelectionListener(boolean b) {
			this.b = b;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org
		 * .eclipse.swt.events.SelectionEvent)
		 */
		@Override
		public void widgetDefaultSelected(SelectionEvent e) {
			dialogChanged();
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse
		 * .swt.events.SelectionEvent)
		 */
		@Override
		public void widgetSelected(SelectionEvent e) {
			guiRequired = b;
			dialogChanged();
		}

	}

	private class PluginTypeSelectionListener implements SelectionListener {

		private PluginType type;

		private PluginTypeSelectionListener(PluginType type) {
			this.type = type;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org
		 * .eclipse.swt.events.SelectionEvent)
		 */
		@Override
		public void widgetDefaultSelected(SelectionEvent e) {
			dialogChanged();
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse
		 * .swt.events.SelectionEvent)
		 */
		@Override
		public void widgetSelected(SelectionEvent e) {
			if (this.type == PluginType.source) {
				setElementsActive(false);
			} else {
				if (pluginType == PluginType.source)
					setElementsActive(true);
			}
			pluginType = type;
			dialogChanged();
		}
	}

	private class QkwSelectionListener implements SelectionListener {

		private QueryKeyword qkw;

		private QkwSelectionListener(QueryKeyword qkw) {
			this.qkw = qkw;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org
		 * .eclipse.swt.events.SelectionEvent)
		 */
		@Override
		public void widgetDefaultSelected(SelectionEvent e) {
			dialogChanged();
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse
		 * .swt.events.SelectionEvent)
		 */
		@Override
		public void widgetSelected(SelectionEvent e) {
			queryKeyword = qkw;
			dialogChanged();
		}

	}

	/**
	 * void setElementsActive
	 * 
	 * @param b
	 */
	private void setElementsActive(boolean b) {
		if (!b) {
			if (this.managedObserver == null) {
				this.managedObserver = true;
			}
			if (this.queryKeyword == null) {
				this.queryKeyword = QueryKeyword.ALL;
			}
		}
		if (b) {
			this.managedObserver = null;
			this.queryKeyword = null;
		}
		// handle obs buttons
		this.obsTrueButton.setSelection(false);
		this.obsFalseButton.setSelection(false);
		this.obsFalseButton.setEnabled(b);
		this.obsTrueButton.setEnabled(b);

		// handle file extension text
		this.fileExtensionText.setText("");
		this.fileExtensionText.setEnabled(!b);

		// handle query keyword buttons
		this.qkwAllAndPersistButton.setSelection(false);
		this.qkwAllButton.setSelection(false);
		this.qkwLastButton.setSelection(false);
		this.qkwSourceButton.setSelection(false);
		this.qkwToolButton.setSelection(false);
		this.qkwUserButton.setSelection(false);
		this.qkwAllAndPersistButton.setEnabled(b);
		this.qkwAllButton.setEnabled(b);
		this.qkwLastButton.setEnabled(b);
		this.qkwSourceButton.setEnabled(b);
		this.qkwToolButton.setEnabled(b);
		this.qkwUserButton.setEnabled(b);
	}

}
