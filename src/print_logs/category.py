import matplotlib.pyplot as plt

# Data
sizes = [9,14,24,28]
labels = [
    'Algebra\n(9 Problems)',
    'Number Theory\n(14 Problems)',
    'Geometry\n(24 Problems)',
    'Combinatorics\n(28 Problems)'
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
    'src/print_logs/category/category.pdf',
    bbox_inches='tight',
    pad_inches=0.3,
    dpi=300
)

plt.show()
