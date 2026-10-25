import matplotlib.pyplot as plt

# Data
sizes = [15, 15, 33, 12]
labels = [
    'AIME I 2026\n(15 Problems)',
    'AIME II 2026\n(15 Problems)',
    'HMMT Feb 2026\n(33 Problems)',
    'APEX 2026\n(12 Problems)'
]

colors = ['red', 'steelblue', 'green', 'purple']

explode = [0.02] * 4

fig, ax = plt.subplots(figsize=(8, 8))

ax.pie(
    sizes,
    labels=labels,
    colors=colors,
    explode=explode,
    startangle=120,

    # Put labels inside
    labeldistance=0.55,

    wedgeprops={
        'edgecolor': 'white',
        'linewidth': 4
    },

    textprops={
        'fontsize': 14,
        'fontweight': 'bold',
        'color': 'white',
        'ha': 'center'
    }
)

ax.set_aspect('equal')

plt.tight_layout()

plt.savefig(
    'src/print_logs/problem_source/problem_source.pdf',
    bbox_inches='tight',
    pad_inches=0.3,
    dpi=300
)

plt.show()
