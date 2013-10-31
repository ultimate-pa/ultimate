package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import org.eclipse.jface.preference.PreferenceNode;

public class UltimatePreferenceNode extends PreferenceNode {

	
	private UltimateGeneratedPreferencePage mCachedPage;
	
	public UltimatePreferenceNode(String id, UltimateGeneratedPreferencePage preferencePage) {
		super(id, preferencePage);
		mCachedPage = preferencePage;
		setPage(mCachedPage);
	}

	@Override
	public void createPage() {
		UltimateGeneratedPreferencePage p = mCachedPage.copy();
		setPage(p);
	}
	
	@Override
	public String getLabelText() {
		return mCachedPage.getTitle();
	}
	
	
	
	

}
