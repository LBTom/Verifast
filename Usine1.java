class Tache
{

	private int temps_necessaire;
	
	private int gain;
	
	public Tache(int t,int g)
	{
		this.temps_necessaire = t;
		this.gain = g;
	}
	
	public int get_gain()

	{
		return this.gain;
	}
	
	public int get_temps_necessaire()
	{
		return this.temps_necessaire;
	}
}