/*@predicate tache(Tache tache; int temps_necessaire, int gain) = 
	     tache.temps_necessaire |-> temps_necessaire &*& 
	     tache.gain |-> gain &*&
	     temps_necessaire > 0 &*& 
	     gain > 0; 

@*/
class Tache
{

	private int temps_necessaire;
	
	private int gain;
	
	public Tache(int t,int g)
	//@requires t>0 && g>0;
	//@ensures tache(this, t, g);
	{
		this.temps_necessaire = t;
		this.gain = g;
	}
	
	public int get_gain()
	//@requires tache(this, ?temps_necessaire,?gain);
	//@ensures tache(this, temps_necessaire, gain) &*& result == gain;
	{
		return this.gain;
	}
	
	public int get_temps_necessaire()
	//@requires tache(this, ?temps_necessaire, ?gain);
	//@ensures tache(this, temps_necessaire, gain) &*& result == temps_necessaire;
	{
		return this.temps_necessaire;
	}
}

/*@
predicate travailleur(Travailleur travailleur;int temps_dispo, int salaire_horaire, int salaire_percu) = 
	  travailleur.temps_dispo |-> temps_dispo &*& 
	  travailleur.salaire_horaire |-> salaire_horaire &*& 
	  travailleur.salaire_percu |-> salaire_percu &*&
	  temps_dispo>=0 &*& 
	  salaire_horaire >= 0 &*& 
	  salaire_percu>=0;
@*/
class Travailleur
{
	private int temps_dispo;
	
	private int salaire_horaire;
	
	private int salaire_percu;

	public Travailleur(int t,int s)
	//@requires t>=0 && s >=0;
	//@ensures travailleur(this,t,s,0); 
	{
		this.temps_dispo = t;
		this.salaire_horaire = s;
		this.salaire_percu = 0;
	}
	
	public int get_temps_dispo()
	//@requires travailleur(this,?temps_dispo,?salaire_horaire,?salaire_percu);
	//@ensures travailleur(this, temps_dispo, salaire_horaire, salaire_percu) &*& result == temps_dispo;
	{
		return this.temps_dispo;
	}
	
	public int get_salaire_horaire()
	//@requires travailleur(this, ?temps_dispo, ?salaire_horaire, ?salaire_percu);
	//@ensures travailleur(this, temps_dispo, salaire_horaire, salaire_percu) &*& result == salaire_horaire;
	{
		return this.salaire_horaire;
	}
	
	public int get_salaire_percu()
	//@requires travailleur(this, ?temps_dispo, ?salaire_horaire, ?salaire_percu);
	//@ensures travailleur(this, temps_dispo, salaire_horaire, salaire_percu) &*& result == salaire_percu;
	{
		return this.salaire_percu;
	}
	
	public int travailler(int t)
	/*@requires travailleur(this, ?temps_dispo, ?salaire_horaire, ?salaire_percu) &*& 
		    t > 0 &*& 
		    t <= temps_dispo &*&
		    salaire_percu + (t *salaire_horaire)>=0;
	@*/
	
	/*@ensures travailleur(this, temps_dispo-t, salaire_horaire, (salaire_percu + (t * salaire_horaire))) &*& 
		   result == (t * salaire_horaire);
	@*/
	{
		this.salaire_percu = this.salaire_percu + (t * this.salaire_horaire);
		this.temps_dispo = this.temps_dispo - t;
		return (t*this.salaire_horaire);
	}
}

/*@
predicate usine(Usine usine; int gain, int depense) = usine.gain |-> gain &*&
usine.depense |-> depense;
@*/
//@predicate estEmbauche(Usine usine,Travailleur travailleur) = true;
class Usine
{
	private int gain;
 	private int depense;
	
	public Usine(int depot_initial)
	//@requires true;
	//@ensures usine(this, depot_initial , 0);
	{
		this.gain = depot_initial;
  		this.depense = 0;
	}
	
	 public int get_gain()
 	//@ requires usine(this,?g,?d);
 	//@ ensures usine(this,g,d) &*& result == g;
 	{
  		return gain;
 	}

 	public int get_depense()
 	//@ requires usine(this,?g,?d);
	//@ ensures usine(this,g,d) &*& result == d;
 	{
 		return depense;
 	}
	
	public int get_balance()
	//@ requires usine(this,?gain,?depense);
 	//@ ensures usine(this,gain,depense) &*& result == (gain - depense);
	{	
 	 	return (this.gain - this.depense);
 	}
	
	public void depose_argent(int argent)
	//@ requires usine(this,?gain,?depense);
	//@ensures (argent > 0) ? usine(this, gain + argent, depense) : usine(this, gain, depense - argent);
	{
		if(argent>0)
			this.gain += argent;
		else
			this.depense -= argent;
	}
	
	public void embaucher(Travailleur travailleur)
	/*@ requires travailleur(travailleur,?temps_dispo,?salaire_horaire,
		?salaire_percu);@*/
	/*@ ensures travailleur(travailleur,temps_dispo,salaire_horaire,salaire_percu) &*&
		estEmbauche(this,travailleur);@*/
	{
		//@close estEmbauche(this,travailleur);
	}
	
	public void licencier(Travailleur travailleur)
		/*@ requires travailleur(travailleur,?temps_dispo,?salaire_horaire,
		?salaire_percu) &*&
		estEmbauche(this,travailleur);@*/
	/*@ ensures travailleur(travailleur,temps_dispo,salaire_horaire,salaire_percu);@*/
	{
		//@close estEmbauche(this,travailleur);
	}
	
	
	public void effectuer_tache(Tache tache,Travailleur travailleur)
	/*@ requires usine(this,?gainU,?depense) &*& 
		    tache(tache, ?temps_necessaire, ?gain) &*& 
		    travailleur(travailleur, ?temps_dispo, ?salaire_horaire, ?salaire_percu) &*& 
		    temps_dispo >= temps_necessaire &*&
		    salaire_percu + (temps_necessaire * salaire_horaire)>=0 &*&
		    estEmbauche(this,travailleur);
	@*/
	/*@ensures (gain > (temps_necessaire * salaire_horaire) ? 
			usine(this, gainU+gain, depense+(temps_necessaire*salaire_horaire)) 
			: 
			usine(this, gainU, depense))
		&*&
		   	(gain > (temps_necessaire * salaire_horaire) ? 
		   		travailleur(travailleur, temps_dispo-temps_necessaire, salaire_horaire, salaire_percu + salaire_horaire*temps_necessaire)
		   		: 
		   		travailleur(travailleur, temps_dispo, salaire_horaire, salaire_percu))
		// &*& tache(tache, temps_necessaire, gain);
		&*&
		estEmbauche(this,travailleur);
	@*/
	{
		if(est_rentable( tache, travailleur)){
			//@open tache(tache,_,_);
			//@open travailleur(travailleur,_,_,_);
			int salaire = travailleur.travailler(tache.get_temps_necessaire());
			this.depense += salaire;
			this.gain += tache.get_gain();
			//@close tache(tache,_,_);
			//@close travailleur(travailleur,_,_,_);
		}
		
	}
	
	public static boolean est_rentable(Tache tache,Travailleur travailleur)
	/*@requires tache(tache, ?temps_necessaire, ?gain) &*& 
		    travailleur(travailleur, ?temps_dispo, ?salaire_horaire, ?salaire_percu);
	@*/
	
	/*@ensures  tache(tache, temps_necessaire, gain) &*&
		    travailleur(travailleur, temps_dispo, salaire_horaire, salaire_percu) &*&
		    result == (gain > (temps_necessaire*salaire_horaire) ? true : false);
	@*/
	{
		//@open tache(tache,_,_);
		//@open travailleur(travailleur,_,_,_);
		return (tache.get_gain() > (tache.get_temps_necessaire() * travailleur.get_salaire_horaire()));
		//@close tache(tache,_,_);
		//@close travailleur(travailleur,_,_,_);
	}
}

class UsineTest
{
	public static void main(String args[])
	//@requires true;
	//@ensures true;	
	{
		
		/*---------------    Test pour Tache    ---------------*/
		
		Tache task = new Tache(1, 100);
		int tn = task.get_temps_necessaire();
		int gain = task.get_gain();
		
		assert ( tn == 1 );
		assert ( gain == 100 );
		
		/*--------------- Test pour Travailleur ---------------*/
		
		Travailleur worker = new Travailleur(35, 15);
		int td = worker.get_temps_dispo(); 
		int sh = worker.get_salaire_horaire();
		int sp = worker.get_salaire_percu();
		
		assert ( td == 35 );
		assert ( sh == 15 );
		assert ( sp == 0 );
		
		worker.travailler(1);
		sp = worker.get_salaire_percu();
		
		assert ( sp == 15 );
		
		
		/*---------------    Test pour Usine    ---------------*/
		
		Usine factory = new Usine(4000);
		int b = factory.get_balance(); 
		
		assert ( b == 4000 );
		factory.depose_argent(1000);
		b = factory.get_balance();
		assert ( b == 5000 );
		
		factory.embaucher(worker);
		factory.effectuer_tache(task, worker);
		b = factory.get_balance();
		assert ( b == 5085 );
		
		Tache task2 = new Tache(1,100);
		factory.effectuer_tache(task2,worker);
		
		// Test licenciement
		
		/*factory.licencier(worker);
		Tache task3 = new Tache(1,100);
		factory.effectuer_tache(task3,worker);*/
		
		// Test temps de travail
		
		/*Travailleur worker2 = new Travailleur(1,10);
		Tache task4 = new Tache(1,100);
		factory.embaucher(worker2);
		factory.effectuer_tache(task4,worker2);
		Tache task5 = new Tache(1,100);
		factory.effectuer_tache(task5,worker2);*/
					
	}
}