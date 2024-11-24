import PropTypes from 'prop-types';


function calculateAge(date) {
    const defaultValue = 'desconocido (scary)';
    const secondsInInterval = {
        'año': 31536000,
        'mes': 2592000,
        'día': 86400,
        'hora': 3600,
        'minuto': 60,
        'segundo': 1,
    };
    const seconds = Math.floor(((new Date()).getTime() - date) / 1000);

    for (const key in secondsInInterval) {
        const interval = seconds / secondsInInterval[key];

        if (interval > 1) {
            const displayValue = Math.floor(interval);
            const displayTimespan = ` ${key}${(key === 'mes' && displayValue > 1) ? 'e' : ''}${(displayValue > 1) ? 's' : ''}`;
            return displayValue + displayTimespan;
        }
    }
    
    return defaultValue;
}

function cropName(name) {
    const maxLength = 14;
    const trailingString = '...';

    if (name.length > maxLength) {
        return name.slice(0, maxLength - trailingString.length) + trailingString;
    }

    return name;
}

export default function Cat({catName, creationDate, variation}) {
    const age = calculateAge(creationDate.getTime());
    const imageSource = `/assets/cat-icons/${variation}.png`;

    return (
        <div className='cat'>
            <img className='cat-icon' src={imageSource} alt={catName} />
            <h3 className='cat-name'>{cropName(catName)}</h3>
            <p className='cat-age'>Edad: {age}</p>
        </div>
    );
}

Cat.propTypes = {
    catName: PropTypes.string.isRequired,
    creationDate: PropTypes.instanceOf(Date).isRequired,
    variation: PropTypes.string.isRequired
};
