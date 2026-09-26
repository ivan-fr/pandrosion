from improve import *
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def main():
 d=json.loads((P/'results.json').read_text());h=[j for j in d['jobs'] if j['split']=='heldout']
 fig,ax=plt.subplots(figsize=(7,5),layout='constrained')
 x=np.array([j['old']['window_error']*1e6 for j in h]);y=np.array([j['r2']['window_error']*1e6 for j in h]);ax.scatter(x,y,c=np.where(y<x,'#247a58','#c5443b'),s=45);ax.plot([.01,1e5],[.01,1e5],'--',color='gray');ax.set(xscale='log',yscale='log',xlabel='R1 : erreur relative (ppm)',ylabel='R2 : erreur relative (ppm)',title='24 cas distincts : 21 améliorations, 3 régressions',xlim=(100,30000),ylim=(.01,30000));ax.text(150,.02,'Sous la diagonale : R2 plus précise',fontsize=9);fig.savefig(P/'validation.png',dpi=160);plt.close(fig)
 text=['# Mesures R2, après gel de la procédure','', '| p | X | Groupe | R1, ppm | R2, ppm | Facteur R1/R2 |','|---:|---:|---|---:|---:|---:|']
 for j in d['jobs']:
  old=j['old']['window_error'];new=j['r2']['window_error'];text.append(f'| {j["p"]:.9g} | {j["X"]:g} | {j["split"]} | {old*1e6:.7g} | {new*1e6:.7g} | {old/new:.5g} |')
 text+=['','Erreurs maximales sur la dernière fenêtre de 20 % du transitoire, dans les deux versions. Calibration nominale avant mesure ; le démarrage à zéro ne fait pas partie de ces points de fonctionnement DC. Les essais de démarrage et de température sont dans [stress.json](stress.json).','']
 (P/'MEASUREMENTS.md').write_text('\n'.join(text))
if __name__=='__main__':main()
